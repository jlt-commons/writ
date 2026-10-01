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
  - After each propagation the simplex checks the inequalities that hold,
    from the tableau of the level below.  An infeasible set is a theory
    conflict: its Farkas combination refutes the clause of their negations,
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
  LRAT checkers do for SAT solvers."
  (:require [writ.solve.pre :refer [negate]]
            [writ.solve.simplex :as simplex]
            [writ.solve.cert :as cert]))

;; --- atoms and values -------------------------------------------------------------

(defn- atom-of
  "The literal of l's pair that is the atom: a boolean's variable, or of an
  inequality and its negation the one whose first coefficient is positive."
  [l]
  (case (first l)
    :bool [:bool (second l) true]
    :le (let [[_ a _] l
              k (key (first (sort-by (comp str key) a)))]
          (if (pos? (get a k)) l (negate l)))))

(defn- value
  "true, false or nil: l under the assignment."
  [st l]
  (get (:val st) l))

(defn- assign
  "Make l true at the current level, for reason r (a clause index, or nil
  for a decision)."
  [st l r]
  (let [n (:neg-of st)
        nl (or (get n l) (negate l))
        a (atom-of l)]
    (-> st
        (assoc-in [:val l] true)
        (assoc-in [:val nl] false)
        (assoc-in [:level a] (count (:lims st)))
        (assoc-in [:reason a] r)
        (assoc-in [:phase a] (= a l))
        (update :trail conj l))))

(defn- budget! [st]
  (when (> (+ (:conflicts st) (:decisions st)) (:budget st))
    (throw (ex-info (str "the budget of " (:budget st) " decisions is exhausted")
                    {:writ.solve.search/budget true}))))

;; --- clauses and watches ----------------------------------------------------------

(defn- watch [st i l] (update-in st [:watch l] (fnil conj []) i))

(defn- add-clause
  "Add clause c with justification just (nil for an original clause),
  watching its first two literals.  Returns [st index]."
  [st c just]
  (let [i (count (:clauses st))
        st (-> st (update :clauses conj c) (cond-> just (update :lemmas conj [c just])))
        ;; a unit clause is asserted at level 0 and stays: nothing to watch
        st (if (next c) (reduce (fn [st l] (watch st i l)) st (take 2 c)) st)]
    [st i]))

(defn- propagate
  "Unit propagation from the literals assigned since :qhead.  Returns st,
  with :conflict set to a clause index when a clause is false."
  [st]
  (loop [st st]
    (if (or (:conflict st) (>= (:qhead st) (count (:trail st))))
      st
      (let [l (nth (:trail st) (:qhead st))
            fl (negate l)                      ; the literal just made false
            ws (get-in st [:watch fl])
            st (-> st (update :qhead inc) (assoc-in [:watch fl] []))
            st (reduce
                (fn [st i]
                  (if (:conflict st)
                    (watch st i fl)
                    (let [c (nth (:clauses st) i)
                          ;; keep the false watch second
                          c (if (= fl (first c)) (into [(second c) fl] (drop 2 c)) c)
                          other (first c)]
                      (if (true? (value st other))
                        (-> st (assoc-in [:clauses i] c) (watch i fl))
                        (if-let [j (first (keep-indexed (fn [j x] (when (and (> j 1) (not (false? (value st x)))) j)) c))]
                          ;; a new watch: swap it into place
                          (let [nw (nth c j)
                                c (assoc c 1 nw j fl)]
                            (-> st (assoc-in [:clauses i] c) (watch i nw)))
                          (let [st (-> st (assoc-in [:clauses i] c) (watch i fl))]
                            (if (false? (value st other))
                              (assoc st :conflict i)
                              (assign st other i))))))))
                st ws)]
        (recur st)))))

;; --- conflict analysis ------------------------------------------------------------

(defn- bump [st a]
  (let [act (+ (get-in st [:activity a] 0.0) (:inc st))]
    (if (> act 1e100)
      (-> st (update :activity (fn [m] (update-vals m #(* % 1e-100)))) (update :inc * 1e-100))
      (assoc-in st [:activity a] act))))

(defn- analyze
  "The first-UIP clause learned from conflict clause index ci, and the level
  to jump back to.  [st learned level]."
  [st ci]
  (let [level (count (:lims st))
        lvl #(get-in st [:level (atom-of %)])]
    (loop [st st, c (nth (:clauses st) ci), seen #{}, out [], counter 0, idx (dec (count (:trail st))), p nil]
      (let [[st seen out counter]
            (reduce (fn [[st seen out counter] q]
                      (let [a (atom-of q)]
                        (if (or (= a (and p (atom-of p))) (contains? seen a) (zero? (lvl q)))
                          [st seen out counter]
                          (let [st (bump st a) seen (conj seen a)]
                            (if (= level (lvl q))
                              [st seen out (inc counter)]
                              [st seen (conj out q) counter])))))
                    [st seen out counter] c)
            ;; the next assigned literal of this level that the clause reached
            idx (loop [i idx] (if (contains? seen (atom-of (nth (:trail st) i))) i (recur (dec i))))
            t (nth (:trail st) idx)
            counter (dec counter)]
        (if (zero? counter)
          (let [learned (into [(negate t)] out)
                back (reduce max 0 (map lvl out))]
            [(update st :inc / 0.95) learned back])
          (recur st (nth (:clauses st) (get-in st [:reason (atom-of t)])) seen out counter (dec idx) t))))))

(defn- truncate
  "The first n elements of vector v, by popping the rest: jolt's subvec
  just past a trie boundary (1025 elements and more) makes a vector whose
  next conj throws, and a trail is conj'd onto after every backjump.  The
  pops cost what the conjs that made them did."
  [v n]
  (loop [v v] (if (> (count v) n) (recur (pop v)) v)))

(defn- backjump
  "Undo every assignment above level k."
  [st k]
  (if (>= k (count (:lims st)))
    st
    (let [cut (nth (:lims st) k)
          gone (subvec (:trail st) cut)
          st (reduce (fn [st l]
                       (let [a (atom-of l)]
                         (-> st
                             (update :val dissoc l (negate l))
                             (update :level dissoc a)
                             (update :reason dissoc a))))
                     st gone)]
      (-> st
          (assoc :trail (truncate (:trail st) cut) :qhead cut :lims (truncate (:lims st) k))
          (assoc :tabs (truncate (:tabs st) (inc k)))))))

(defn- learn
  "Learn clause c (justified by just) after a conflict, jump back and assert
  its first literal.  Returns st, or {:unsat st} for the empty clause."
  [st c just back]
  (if (empty? c)
    {:unsat (second (add-clause st c just))
     :st (first (add-clause st c just))}
    (let [st (backjump st back)
          ;; the asserting literal first, then one of the highest level
          c (if (next c)
              (let [lvl #(get-in st [:level (atom-of %)] -1)
                    j (apply max-key #(lvl (nth c %)) (range 1 (count c)))]
                (assoc c 1 (nth c j) j (nth c 1)))
              c)
          [st i] (add-clause st c just)]
      (assign (assoc st :conflict nil) (first c) i))))

;; --- the theory -------------------------------------------------------------------

(defn- theory
  "The simplex over the inequalities that hold, from the level's tableau."
  [st]
  (let [lits (filter #(= :le (first %)) (:trail st))
        from (peek (:tabs st))]
    (simplex/check lits (:max-pivots st) from)))

;; --- the search -------------------------------------------------------------------

(defn- luby
  "The i-th term of Luby's sequence 1 1 2 1 1 2 4 ..., as MiniSat has it."
  [i]
  (let [[size sq] (loop [size 1, sq 0] (if (< size (inc i)) (recur (inc (* 2 size)) (inc sq)) [size sq]))]
    (loop [x i, size size, sq sq]
      (if (= (dec size) x)
        (bit-shift-left 1 sq)
        (let [size (quot (dec size) 2)] (recur (mod x size) size (dec sq)))))))

(defn- decide
  "The unassigned atom of highest activity, as the literal of its saved
  phase, or nil when every atom is assigned."
  [st]
  (let [free (remove #(some? (value st %)) (:atoms st))]
    (when (seq free)
      (let [a (apply max-key #(get-in st [:activity %] 0.0) free)]
        (if (get-in st [:phase a] false) a (negate a))))))

(defn- conflict-step
  "Handle the conflict of clause ci, every literal of which is false: learn
  from it, or finish with unsat.  A clause whose literals were all assigned
  below the current level -- a theory conflict the level below did not see --
  is analysed from its own highest level."
  [st ci]
  (let [c (nth (:clauses st) ci)
        top (reduce max 0 (map #(get-in st [:level (atom-of %)] 0) c))]
    (if (zero? top)
      ;; a conflict with nothing decided: the empty clause follows by RUP
      {:unsat (first (add-clause st [] {:rup true}))}
      (let [st (backjump st top)
            [st c back] (analyze st ci)]
        (learn (update st :conflicts inc) c {:rup true} back)))))

(defn- start [clauses {:keys [budget max-pivots]}]
  (let [atoms (vec (distinct (map atom-of (mapcat identity clauses))))
        st {:clauses [] :lemmas [] :watch {} :val {} :level {} :reason {} :phase {}
            :activity {} :inc 1.0 :trail [] :qhead 0 :lims [] :tabs [nil]
            :atoms atoms :conflicts 0 :decisions 0 :budget budget :max-pivots max-pivots :cuts 0}]
    (reduce (fn [st c]
              (if (:unsat st)
                st
                (case (count c)
                  0 {:unsat (first (add-clause st [] nil))}
                  1 (let [[st i] (add-clause st c nil)
                          l (first c)]
                      (case (value st l)
                        true st
                        false {:unsat st :level0-conflict i}
                        (assign st l i)))
                  (first (add-clause st c nil)))))
            st clauses)))

(defn- search
  "Search one component's clauses for a model.  {:sat true :assign #{literal} :values {var
  int}} or {:lemmas [[clause justification] ...]} ending with the empty
  clause; throws when the budget of conflicts is spent."
  [clauses opts]
  (let [st0 (start clauses opts)]
    (if (:unsat st0)
      {:lemmas (conj (:lemmas (:unsat st0)) [[] {:rup true}])}
      (loop [st st0, restarts 0, until (* 64 (luby 0))]
        (budget! st)
        (let [st (propagate st)]
          (cond
            (:unsat st) {:lemmas (:lemmas (:unsat st))}

            (:conflict st)
            (let [r (conflict-step st (:conflict st))]
              (if (:unsat r)
                {:lemmas (:lemmas (:unsat r))}
                (recur r restarts until)))

            :else
            (let [t (theory st)]
              (if-let [fk (:conflict t)]
                ;; a theory conflict: learn the negations of the bounds, whose
                ;; Farkas combination refutes them
                (let [fk (vec (remove #(zero? (second %)) fk))
                      c (vec (distinct (map (comp negate first) fk)))
                      [st i] (add-clause st c {:farkas fk})
                      r (conflict-step st i)]
                  (if (:unsat r)
                    {:lemmas (:lemmas (:unsat r))}
                    (recur r restarts until)))
                (let [st (assoc st :tabs (conj (pop (:tabs st)) (:tableau t)))]
                  (cond
                    ;; restart: back to level 0, keeping what was learned
                    (>= (:conflicts st) until)
                    (let [restarts (inc restarts)]
                      (recur (backjump st 0) restarts (+ (:conflicts st) (* 64 (luby restarts)))))

                    :else
                    (if-let [l (decide st)]
                      (recur (-> st
                                 (update :decisions inc)
                                 (update :lims conj (count (:trail st)))
                                 (update :tabs conj (peek (:tabs st)))
                                 (assign l nil))
                             restarts until)
                      ;; every atom assigned and the theory agrees: integral?
                      (if-let [[x v] (first (remove #(integer? (val %)) (sort-by (comp str key) (:sat t))))]
                        (let [terms (when (< (:cuts st) 12) (simplex/gomory (:tableau t)))]
                          (if (and terms (nil? (value st (cert/cut (set (:trail st)) terms))))
                            ;; a Gomory cut: the bounds it combines imply it
                            (let [cl (cert/cut (set (:trail st)) terms)
                                  c (into [cl] (map (comp negate first) terms))
                                  [st i] (add-clause (update st :cuts inc) c {:cut terms :lit cl})
                                  st (update st :atoms conj (atom-of cl))]
                              (recur (assign st cl i) restarts until))
                            ;; branch: x <= floor v, a new atom, decided
                            (let [b [:le {x 1} (simplex/floor-value v)]
                                  st (update st :atoms conj (atom-of b))]
                              (recur (-> st
                                         (update :decisions inc)
                                         (update :lims conj (count (:trail st)))
                                         (update :tabs conj (peek (:tabs st)))
                                         (assign b nil))
                                     restarts until))))
                        {:sat true :assign (set (:trail st)) :values (:sat t)}))))))))))))

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
              (recur (rest parts) (-> acc (update :assign into (:assign r)) (update :values merge (:values r))))
              r))
          acc)))))
