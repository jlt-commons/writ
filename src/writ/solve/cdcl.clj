(ns writ.solve.cdcl
  "Conflict-driven clause learning modulo linear integer arithmetic: the
  DPLL(T) search of Nieuwenhuis, Oliveras and Tinelli, with the simplex of
  Dutertre and de Moura as its theory, as SMT solvers do it.

  - Unit propagation over two watched literals per clause.
  - On a conflict, the first-UIP clause is learned and the search jumps back
    to the level where it becomes unit, not merely to the last decision.
  - Decisions take the unassigned atom of highest activity (VSIDS): every
    atom in a learned clause is bumped, and all activities decay, so the
    search keeps to the atoms recent conflicts were about.  An atom is
    decided with the value it last had (phase saving).
  - Restarts follow Luby's sequence; learned clauses survive them.
  - Each inequality made true goes to the simplex (writ.solve.lra) as a
    bound, and after each propagation the simplex checks them; a backjump
    takes the bounds of the literals it undoes back out.  An infeasible
    set is a theory conflict: its Farkas combination refutes the clause of their negations,
    which is learned like any other.  A fractional value is branched on
    (x <= floor v, as a decision) or cut (a Gomory cut, learned as a lemma).

  - Before any of it, the clauses are split into independent components --
    sets sharing no variable -- as KLEE's constraint independence does, and
    each is solved alone, the smallest first: the clauses are unsatisfiable
    when one component is, and a model is the union of the components'.

  None of it is trusted.  An unsat answer carries the learned clauses, in
  order, each with what justifies it -- reverse unit propagation from the
  clauses before it, a Farkas combination, or a cut -- ending with the empty
  clause.  writ.solve.cert checks that list without searching, as DRUP and
  LRAT checkers do for SAT solvers.

  Inside a search a literal is a number -- atom k's literal is 2k, its
  negation 2k+1 -- and the assignment, the watches and the activities are
  arrays indexed by it, mutated in place: a step looks a literal up without
  hashing it.  The literals themselves come back in the lemmas and the
  model.  The unassigned atoms wait in a binary heap, highest activity on
  top; an atom assigned stays in it until a decision finds it there."
  (:require [writ.solve.pre :refer [negate]]
            [writ.solve.simplex :as simplex]
            [writ.solve.lra :as lra]
            [writ.solve.cert :as cert]))

;; --- atoms -----------------------------------------------------------------------

(defn- atom-of
  "The literal of l's pair that is the atom: a boolean's variable, or of an
  inequality and its negation the one whose first coefficient is positive."
  [l]
  (case (first l)
    :bool [:bool (second l) true]
    :le (let [[_ a _] l
              k (key (first (sort-by (comp str key) a)))]
          (if (pos? (get a k)) l (negate l)))))

(defn- var-of
  "The atom of literal number l."
  [l]
  (bit-shift-right l 1))

;; --- one search's state -----------------------------------------------------------
;;
;; Arrays by literal number: :val (true, false or nil) and :watch (the clauses
;; watching it).  By atom: :level, :reason (a clause index, nil for a
;; decision), :phase, :act and :hpos (its place in the heap, nil when out).

(defn- state [budget max-pivots]
  {:ids (volatile! {}) :lits (volatile! [])
   :val (volatile! (object-array 64)) :watch (volatile! (object-array 64))
   :level (volatile! (object-array 32)) :reason (volatile! (object-array 32))
   :phase (volatile! (object-array 32)) :act (volatile! (object-array 32))
   :hpos (volatile! (object-array 32)) :heap (volatile! (object-array 32)) :hsize (volatile! 0)
   :trail (volatile! (object-array 32)) :tsize (volatile! 0) :qhead (volatile! 0)
   :clauses (volatile! []) :lemmas (volatile! [])
   :lims (volatile! [])
   ;; the theory, and the place on the trail up to which it has the literals
   :lra (lra/make max-pivots) :apos (volatile! 0)
   :inc (volatile! 1.0) :conflicts (volatile! 0) :decisions (volatile! 0) :cuts (volatile! 0)
   :budget budget :max-pivots max-pivots})

(defn- grow!
  "Make the array in volatile v at least n long."
  [v n]
  (let [^objects a @v]
    (when (< (alength a) n)
      (let [b (object-array (max n (* 2 (alength a))))]
        (System/arraycopy a 0 b 0 (alength a))
        (vreset! v b)))))

(defn- value
  "true, false or nil: literal number l under the assignment."
  [s l]
  (aget ^objects @(:val s) l))

;; --- the heap of atoms decisions choose from --------------------------------------

(defn- above?
  "Does atom a come before atom b: higher activity, or of equal activity
  the atom met last?"
  [^objects act a b]
  (let [x (aget act a) y (aget act b)]
    (or (> x y) (and (not (< x y)) (> a b)))))

(defn- heap-set! [s i a]
  (aset ^objects @(:heap s) i a)
  (aset ^objects @(:hpos s) a i))

(defn- sift-up! [s i]
  (let [^objects h @(:heap s) act @(:act s) a (aget h i)]
    (loop [i i]
      (let [p (quot (dec i) 2)]
        (if (and (pos? i) (above? act a (aget h p)))
          (do (heap-set! s i (aget h p)) (recur p))
          (heap-set! s i a))))))

(defn- sift-down! [s i]
  (let [^objects h @(:heap s) act @(:act s) n @(:hsize s) a (aget h i)]
    (loop [i i]
      (let [l (inc (* 2 i)) r (inc l)
            c (cond (>= l n) nil
                    (and (< r n) (above? act (aget h r) (aget h l))) r
                    :else l)]
        (if (and c (above? act (aget h c) a))
          (do (heap-set! s i (aget h c)) (recur c))
          (heap-set! s i a))))))

(defn- heap-insert! [s a]
  (when (nil? (aget ^objects @(:hpos s) a))
    (let [n @(:hsize s)]
      (vreset! (:hsize s) (inc n))
      (heap-set! s n a)
      (sift-up! s n))))

(defn- heap-pop! [s]
  (let [^objects h @(:heap s) a (aget h 0) n (dec @(:hsize s))]
    (aset ^objects @(:hpos s) a nil)
    (vreset! (:hsize s) n)
    (when (pos? n)
      (heap-set! s 0 (aget h n))
      (sift-down! s 0))))

(defn- unassigned? [s a] (nil? (value s (* 2 a))))

;; --- literals ---------------------------------------------------------------------

(defn- intern!
  "Literal l's number.  A new literal is numbered with its negation, and
  its atom joins the atoms decisions choose from."
  [s l]
  (or (get @(:ids s) l)
      (let [a (atom-of l)
            [p n] (if (= a l) [l (negate l)] [a l])
            k (quot (count @(:lits s)) 2)]
        (vswap! (:ids s) assoc p (* 2 k) n (inc (* 2 k)))
        (vswap! (:lits s) conj p n)
        (doseq [v [:val :watch]] (grow! (v s) (* 2 (inc k))))
        (doseq [v [:level :reason :phase :act :hpos :heap :trail]] (grow! (v s) (inc k)))
        (aset ^objects @(:act s) k 0.0)
        (heap-insert! s k)
        (get @(:ids s) l))))

(defn- literal [s l] (nth @(:lits s) l))

(defn- known
  "Literal l's number, or nil when the search has not met it."
  [s l]
  (get @(:ids s) l))

(defn- assign!
  "Make literal number l true at the current level, for reason r (a clause
  index, or nil for a decision)."
  [s l r]
  (let [a (var-of l) ^objects v @(:val s) n @(:tsize s)]
    (aset v l true)
    (aset v (bit-xor l 1) false)
    (aset ^objects @(:level s) a (count @(:lims s)))
    (aset ^objects @(:reason s) a r)
    (aset ^objects @(:phase s) a (even? l))
    (aset ^objects @(:trail s) n l)
    (vreset! (:tsize s) (inc n))))

(defn- budget! [s]
  (when (> (+ @(:conflicts s) @(:decisions s)) (:budget s))
    (throw (ex-info (str "the budget of " (:budget s) " decisions is exhausted")
                    {:writ.solve.search/budget true}))))

(defn- trail [s] (let [^objects t @(:trail s)] (map #(aget t %) (range @(:tsize s)))))

;; --- clauses and watches ----------------------------------------------------------

(defn- watch! [s i l]
  (let [^objects w @(:watch s)] (aset w l (conj (or (aget w l) []) i))))

(defn- add-clause!
  "Add clause c, a vector of literal numbers, with justification just (nil
  for an original clause), watching its first two literals.  Its index."
  [s c just]
  (let [i (count @(:clauses s))]
    (vswap! (:clauses s) conj (object-array c))
    (when just (vswap! (:lemmas s) conj [(mapv #(literal s %) c) just]))
    ;; a unit clause is asserted at level 0 and stays: nothing to watch
    (when (next c) (watch! s i (nth c 0)) (watch! s i (nth c 1)))
    i))

(defn- propagate!
  "Unit propagation from the literals assigned since :qhead.  The index of
  a clause it made false, or nil."
  [s]
  (loop []
    (let [qh @(:qhead s)]
      (if (>= qh @(:tsize s))
        nil
        (let [fl (bit-xor (aget ^objects @(:trail s) qh) 1)   ; the literal just made false
              ^objects w @(:watch s)
              ws (aget w fl)
              cls @(:clauses s)]
          (vreset! (:qhead s) (inc qh))
          (aset w fl [])
          (or (reduce
                (fn [conflict i]
                  (if conflict
                    (do (watch! s i fl) conflict)
                    (let [^objects c (nth cls i)]
                      ;; keep the false watch second
                      (when (= fl (aget c 0)) (aset c 0 (aget c 1)) (aset c 1 fl))
                      (let [other (aget c 0)]
                        (if (true? (value s other))
                          (do (watch! s i fl) nil)
                          (if-let [j (loop [j 2] (cond (>= j (alength c)) nil
                                                       (false? (value s (aget c j))) (recur (inc j))
                                                       :else j))]
                            ;; a new watch: swap it into place
                            (let [nw (aget c j)]
                              (aset c 1 nw) (aset c j fl) (watch! s i nw) nil)
                            (do (watch! s i fl)
                                (if (false? (value s other))
                                  i
                                  (do (assign! s other i) nil)))))))))
                nil (or ws []))
              (recur)))))))

;; --- conflict analysis ------------------------------------------------------------

(defn- bump! [s a]
  (let [^objects act @(:act s)
        x (+ (aget act a) @(:inc s))]
    (if (> x 1e100)
      (let [n (quot (count @(:lits s)) 2)]
        (dotimes [b n] (aset act b (* (aget act b) 1e-100)))
        (vswap! (:inc s) * 1e-100)
        ;; every key moves: the heap rebuilt from the unassigned atoms
        (dotimes [b n] (aset ^objects @(:hpos s) b nil))
        (vreset! (:hsize s) 0)
        (dotimes [b n] (when (unassigned? s b) (heap-insert! s b))))
      (do (aset act a x)
          (when-let [i (aget ^objects @(:hpos s) a)] (sift-up! s i))))))

(defn- analyze!
  "The first-UIP clause learned from conflict clause index ci, and the level
  to jump back to: [learned level]."
  [s ci]
  (let [level (count @(:lims s))
        ^objects levels @(:level s)
        ^objects tr @(:trail s)
        cls @(:clauses s)
        lvl #(aget levels (var-of %))]
    (loop [^objects c (nth cls ci), seen #{}, out [], counter 0, idx (dec @(:tsize s)), p nil]
      (let [pa (when p (var-of p))
            [seen out counter]
            (areduce c k acc [seen out counter]
                     (let [[seen out counter] acc
                           q (aget c k)
                           a (var-of q)]
                       (if (or (= a pa) (contains? seen a) (zero? (lvl q)))
                         acc
                         (do (bump! s a)
                             (if (= level (lvl q))
                               [(conj seen a) out (inc counter)]
                               [(conj seen a) (conj out q) counter])))))
            ;; the next assigned literal of this level that the clause reached
            idx (loop [i idx] (if (contains? seen (var-of (aget tr i))) i (recur (dec i))))
            t (aget tr idx)
            counter (dec counter)]
        (if (zero? counter)
          (do (vswap! (:inc s) / 0.95)
              [(into [(bit-xor t 1)] out) (reduce max 0 (map lvl out))])
          (recur (nth cls (aget ^objects @(:reason s) (var-of t))) seen out counter (dec idx) t))))))

(defn- truncate
  "The first n elements of vector v, by popping the rest: jolt's subvec
  just past a trie boundary (1025 elements and more) makes a vector whose
  next conj throws, and a level's limits are conj'd onto after every
  backjump.  The pops cost what the conjs that made them did."
  [v n]
  (loop [v v] (if (> (count v) n) (recur (pop v)) v)))

(defn- backjump!
  "Undo every assignment above level k."
  [s k]
  (let [lims @(:lims s)]
    (when (< k (count lims))
      (let [cut (nth lims k)
            ^objects tr @(:trail s) ^objects v @(:val s)
            ^objects levels @(:level s) ^objects reasons @(:reason s)]
        (loop [i cut]
          (when (< i @(:tsize s))
            (let [l (aget tr i) a (var-of l)]
              (aset v l nil) (aset v (bit-xor l 1) nil)
              (aset levels a nil) (aset reasons a nil)
              ;; unassigned again: back among the atoms decisions choose from
              (heap-insert! s a)
              (recur (inc i)))))
        (vreset! (:tsize s) cut)
        (vreset! (:qhead s) cut)
        (vreset! (:lims s) (truncate lims k))
        (lra/backtrack! (:lra s) cut)
        (vswap! (:apos s) min cut)))))

(defn- learn!
  "Learn clause c (justified by just) after a conflict, jump back and assert
  its first literal.  :unsat for the empty clause."
  [s c just back]
  (if (empty? c)
    (do (add-clause! s c just) :unsat)
    (do (backjump! s back)
        ;; the asserting literal first, then one of the highest level
        (let [c (if (next c)
                  (let [^objects levels @(:level s)
                        lvl #(or (aget levels (var-of %)) -1)
                        j (apply max-key #(lvl (nth c %)) (range 1 (count c)))]
                    (assoc c 1 (nth c j) j (nth c 1)))
                  c)
              i (add-clause! s c just)]
          (assign! s (first c) i)
          nil))))

;; --- the theory -------------------------------------------------------------------

(defn- theory
  "The simplex given the inequalities assigned since it last looked, and
  checked: nil, or the Farkas certificate of a conflict."
  [s]
  (let [st (:lra s) ^objects tr @(:trail s) end @(:tsize s)]
    (or (loop []
          (let [i @(:apos s)]
            (when (< i end)
              (vreset! (:apos s) (inc i))
              (let [l (literal s (aget tr i))]
                (or (when (= :le (first l)) (lra/assert! st l i))
                    (recur))))))
        (lra/check! st))))

;; --- the search -------------------------------------------------------------------

(defn- luby
  "The i-th term of Luby's sequence 1 1 2 1 1 2 4 ..., as MiniSat has it."
  [i]
  (let [[size sq] (loop [size 1, sq 0] (if (< size (inc i)) (recur (inc (* 2 size)) (inc sq)) [size sq]))]
    (loop [x i, size size, sq sq]
      (if (= (dec size) x)
        (bit-shift-left 1 sq)
        (let [size (quot (dec size) 2)] (recur (mod x size) size (dec sq)))))))

(defn- decide!
  "The unassigned atom of highest activity, as the literal number of its
  saved phase, or nil when every atom is assigned."
  [s]
  (loop []
    (when (pos? @(:hsize s))
      (let [a (aget ^objects @(:heap s) 0)]
        (if (unassigned? s a)
          (if (aget ^objects @(:phase s) a) (* 2 a) (inc (* 2 a)))
          (do (heap-pop! s) (recur)))))))

(defn- conflict-step!
  "Handle the conflict of clause ci, every literal of which is false: learn
  from it, or finish with :unsat.  A clause whose literals were all assigned
  below the current level -- a theory conflict the level below did not see --
  is analysed from its own highest level."
  [s ci]
  (let [^objects c (nth @(:clauses s) ci)
        ^objects levels @(:level s)
        top (areduce c k m 0 (max m (or (aget levels (var-of (aget c k))) 0)))]
    (if (zero? top)
      ;; a conflict with nothing decided: the empty clause follows by RUP
      (do (add-clause! s [] {:rup true}) :unsat)
      (do (backjump! s top)
          (let [[c back] (analyze! s ci)]
            (vswap! (:conflicts s) inc)
            (learn! s c {:rup true} back))))))

(defn- start!
  "The search's state for clauses, every atom numbered in the order the
  clauses name them; :unsat in it when a clause is false from the start."
  [clauses {:keys [budget max-pivots]}]
  (let [s (state budget max-pivots)]
    (doseq [c clauses, l c] (intern! s l))
    (assoc s :unsat
           (reduce (fn [_ c]
                     (case (count c)
                       0 (do (add-clause! s [] nil) (reduced true))
                       1 (let [l (intern! s (first c))
                               i (add-clause! s [l] nil)]
                           (case (value s l)
                             true nil
                             false (reduced true)
                             (do (assign! s l i) nil)))
                       (do (add-clause! s (mapv #(intern! s %) c) nil) nil)))
                   nil clauses))))

(defn- decide-on!
  "A decision: a new level, its tableau the one below's, with literal l."
  [s l]
  (vswap! (:decisions s) inc)
  (vswap! (:lims s) conj @(:tsize s))
  (assign! s l nil))

(defn- search
  "Search one component's clauses for a model.  {:sat true :assign #{literal} :values {var
  int}} or {:lemmas [[clause justification] ...]} ending with the empty
  clause; throws when the budget of conflicts is spent."
  [clauses opts]
  (let [s (start! clauses opts)
        spent #(+ @(:conflicts s) @(:decisions s))
        unsat #(hash-map :lemmas @(:lemmas s) :spent (spent))]
    (if (:unsat s)
      {:lemmas (conj @(:lemmas s) [[] {:rup true}])}
      (loop [restarts 0, until (* 64 (luby 0))]
        (budget! s)
        (if-let [ci (propagate! s)]
          (if (conflict-step! s ci) (unsat) (recur restarts until))
          (let [fk (theory s)]
            (if fk
              ;; a theory conflict: learn the negations of the bounds, whose
              ;; Farkas combination refutes them
              (let [fk (vec (remove #(zero? (second %)) fk))
                    c (vec (distinct (map (comp negate first) fk)))
                    i (add-clause! s (mapv #(intern! s %) c) {:farkas fk})]
                (if (conflict-step! s i) (unsat) (recur restarts until)))
              (do
                (cond
                  ;; restart: back to level 0, keeping what was learned
                  (>= @(:conflicts s) until)
                  (let [restarts (inc restarts)]
                    (backjump! s 0)
                    (recur restarts (+ @(:conflicts s) (* 64 (luby restarts)))))

                  :else
                  (if-let [l (decide! s)]
                    (do (decide-on! s l) (recur restarts until))
                    ;; every atom assigned and the theory agrees: integral?
                    (if-let [[x v] (first (remove #(integer? (val %)) (sort-by (comp str key) (lra/model (:lra s)))))]
                      (let [terms (when (< @(:cuts s) 12) (lra/gomory (:lra s)))
                            cl (when terms (cert/cut (set (map #(literal s %) (trail s))) terms))]
                        (if (and terms (nil? (some->> (known s cl) (value s))))
                          ;; a Gomory cut: the bounds it combines imply it
                          (let [_ (vswap! (:cuts s) inc)
                                c (mapv #(intern! s %) (into [cl] (map (comp negate first) terms)))
                                i (add-clause! s c {:cut terms :lit cl})]
                            (assign! s (first c) i)
                            (recur restarts until))
                          ;; branch: x <= floor v, a new atom, decided
                          (do (decide-on! s (intern! s [:le {x 1} (simplex/floor-value v)]))
                              (recur restarts until))))
                      {:sat true :assign (set (map #(literal s %) (trail s))) :values (lra/model (:lra s))
                       :spent (spent)})))))))))))

;; --- constraint independence -------------------------------------------------------

(defn- vars-of [l]
  (case (first l) :bool [(second l)] :le (keys (second l))))

(defn- components
  "The clauses split into sets that share no variable, smallest first, each
  in the clauses' order."
  [clauses]
  (let [find (fn find [m x] (let [p (get m x x)] (if (= p x) x (find m p))))
        union (fn [m a b] (let [ra (find m a) rb (find m b)] (if (= ra rb) m (assoc m ra rb))))
        m (reduce (fn [m c]
                    (let [vs (mapcat vars-of c)]
                      (if (seq vs) (reduce (fn [m v] (union m (first vs) v)) m vs) m)))
                  {} clauses)
        groups (group-by (fn [c] (if-let [v (first (mapcat vars-of c))] (find m v) ::none)) clauses)]
    (sort-by count (vals groups))))

(defn solve
  "Search clauses for a model.  {:sat true :assign #{literal} :values {var
  int}} or {:lemmas [[clause justification] ...]} ending with the empty
  clause; throws when the budget of decisions and conflicts is spent."
  [clauses opts]
  (let [parts (components clauses)]
    (if (<= (count parts) 1)
      (search clauses opts)
      (loop [parts parts, acc {:sat true :assign #{} :values {}}]
        (if-let [p (first parts)]
          (let [r (search (vec p) opts)]
            (if (:sat r)
              (recur (rest parts) (-> acc (update :assign into (:assign r)) (update :values merge (:values r))
                                      (update :spent (fnil + 0) (:spent r 0))))
              r))
          acc)))))
