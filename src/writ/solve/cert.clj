(ns writ.solve.cert
  "The checker for the solver's unsat certificates.  It searches for
  nothing: it rebuilds the clauses itself, with writ.solve.pre, and walks
  the proof tree the search recorded.

  A certificate is {:claim :unsat|:valid, :proof p}.  A :valid claim is
  about a formula's negation.  A proof is a tree:

    {:split l :yes p :no q}   l is true in p's branch, its negation in q's
    {:clause i}               clause i has every literal false on the branch
    {:cut [[l k] ...] :then p}
                              the inequalities l hold on the branch, and
                              their sum weighted by rationals k >= 0,
                              a.x <= c, has integer coefficients a; then
                              a.x <= floor(c) holds in p's branch too
    {:farkas [[l k] ...]}     the inequalities l hold on the branch, and
                              their sum weighted by rationals k >= 0 is
                              0 <= c for a constant c < 0

  or a list of learned clauses, as a CDCL search derives them:

    {:lemmas [[clause justification] ...]}

  each clause following from the clauses before it (the formula's, then the
  lemmas already checked), by one of

    {:rup true}               reverse unit propagation: with every literal of
                              the clause false, unit propagation over the
                              clauses so far falsifies one of them
    {:farkas [[l k] ...]}     the clause is the negations of the l, whose
                              combination is 0 <= a negative constant
    {:cut [[l k] ...] :lit m} the clause is m and the negations of the l, and
                              m is their Chvatal-Gomory cut

  and the last is the empty clause.  These are the checks a DRUP or LRAT
  proof checker makes for a SAT solver, plus the arithmetic ones.

  Each is plainly sound.  A split covers every integer assignment, since
  over the integers a.x <= c or -a.x <= -c - 1, and a boolean is true or
  false.  A clause false everywhere on a branch leaves the branch without
  a model.  A cut is Chvatal and Gomory's: with integer coefficients the
  left side is an integer, so it is at most the bound rounded down.  And
  a nonnegative sum of true inequalities is true, so one
  that says 0 is at most a negative number cannot be.  So a tree whose
  every leaf checks shows the clauses, and with them the formula, have no
  model.  What must be trusted is this namespace and writ.solve.pre."
  (:require [writ.solve.pre :as pre]))

(defn- reject! [& msg]
  (throw (ex-info (apply str msg) {:writ.solve/rejected true})))

(defn- literal!
  "A split may be on any literal with integer coefficients and bound."
  [l]
  (let [ok (and (vector? l) (= 3 (count l))
                (case (first l)
                  :le (let [[_ a c] l]
                        (and (map? a) (every? integer? (vals a)) (integer? c)))
                  :bool (boolean? (nth l 2))
                  false))]
    (when-not ok (reject! "not a literal: " (pr-str l)))
    l))

(defn combine
  "The sum of the inequalities l weighted by k, [:le a c], a without zeros.
  Each must be true on the branch path."
  [path terms]
  (when-not (and (sequential? terms) (seq terms))
    (reject! "an empty combination of inequalities"))
  (doseq [t terms]
    (let [[l k] (when (and (vector? t) (= 2 (count t))) t)]
      (when-not (and (rational? k) (not (neg? k)))
        (reject! "a multiplier is not a nonnegative rational: " (pr-str t)))
      (when-not (= :le (first l))
        (reject! "a combined term is not an inequality: " (pr-str l)))
      (when-not (contains? path l)
        (reject! "a combined inequality is not true on its branch: " (pr-str l)))))
  (let [sum (reduce (fn [m [[_ a _] k]] (merge-with + m (into {} (map (fn [[x c]] [x (* k c)])) a)))
                    {} terms)]
    [:le (into {} (remove (comp zero? val)) sum)
     (reduce + (map (fn [[[_ _ c] k]] (* k c)) terms))]))

(defn cut
  "The literal a cut with multipliers terms derives on branch path."
  [path terms]
  (let [[_ a c] (combine path terms)]
    (when-not (every? integer? (vals a))
      (reject! "a cut's sum has a fractional coefficient: " (pr-str a)))
    [:le a (if (integer? c) c (let [n (numerator c) d (denominator c)] (quot (- n (mod n d)) d)))]))

(defn- farkas!
  "The weighted inequalities, all true on the branch, sum to 0 <= negative."
  [path terms]
  (let [[_ a c] (combine path terms)]
    (when (seq a)
      (reject! "the Farkas sum leaves variables: " (pr-str a)))
    (when-not (neg? c)
      (reject! "the Farkas sum is 0 <= " c ", which holds"))))

(defn- check!
  "Every branch of proof p closes, the literals in path being true."
  [clauses path p]
  (cond
    (not (map? p)) (reject! "not a proof: " (pr-str p))
    (contains? p :split)
    (let [l (literal! (:split p))]
      (check! clauses (conj path l) (:yes p))
      (check! clauses (conj path (pre/negate l)) (:no p)))
    (contains? p :clause)
    (let [i (:clause p)
          c (when (and (integer? i) (< -1 i (count clauses))) (clauses i))]
      (when-not c (reject! "no clause " (pr-str i)))
      (doseq [l c]
        (when-not (contains? path (pre/negate l))
          (reject! "clause " i " is not false on its branch: " (pr-str l)))))
    (contains? p :cut) (check! clauses (conj path (cut path (:cut p))) (:then p))
    (contains? p :farkas) (farkas! path (:farkas p))
    :else (reject! "not a proof step: " (pr-str p))))

;; --- the clause database unit propagation runs over --------------------------
;;
;; Each literal is numbered once, its negation the same number with the low
;; bit flipped, so propagation compares numbers, not literals.  A clause is a
;; vector of numbers; occ holds, for each number, the clauses it is in.  A
;; clause can turn unit or false only when one of its literals turns false,
;; so propagation visits just the clauses of each literal it falsifies.

(defn- numbering
  "Each literal of the clauses cls a number: {literal n, (negate literal)
  (bit-xor n 1)}."
  [cls]
  (reduce (fn [ids l]
            (if (contains? ids l)
              ids
              (let [n (count ids)] (assoc ids l n (pre/negate l) (inc n)))))
          {} (mapcat identity cls)))

(defn- database
  "An empty clause database over the literals numbered by ids."
  [ids]
  (let [n (count ids)]
    {:ids ids :cls (volatile! []) :occ (object-array n) :units (volatile! [])
     :empty (volatile! false) :val (object-array n)}))

(defn- add!
  "Add clause c to database db."
  [db c]
  (let [{:keys [ids cls occ units empty]} db
        ns (mapv ids c)
        i (count @cls)]
    (vswap! cls conj ns)
    (case (count ns)
      0 (vreset! empty true)
      1 (vswap! units conj (first ns))
      nil)
    (doseq [l (distinct ns)] (aset occ l (conj (or (aget occ l) []) i)))
    db))

(defn- propagates-to-conflict?
  "With the literals numbered ns true, does unit propagation over db
  falsify a clause, or force a literal and its negation?"
  [db ns]
  (let [{:keys [cls occ units empty val]} db
        cls @cls
        trail (volatile! [])
        conflict (volatile! false)
        ;; make literal l true; a literal already false is the conflict
        assign! (fn [l]
                  (cond (aget val l) nil
                        (aget val (bit-xor l 1)) (vreset! conflict true)
                        :else (do (aset val l true) (vswap! trail conj l))))]
    (try
      (if @empty
        true
        (do (run! assign! ns)
            (run! assign! @units)
            (loop [qi 0]
              (cond
                @conflict true
                (>= qi (count @trail)) false
                :else
                (let [f (bit-xor (nth @trail qi) 1)]
                  ;; each clause that has f, which is now false
                  (reduce (fn [_ ci]
                            (let [c (nth cls ci)
                                  ;; the open literals, up to two; :sat when one is true
                                  open (reduce (fn [open l]
                                                 (cond (aget val l) (reduced :sat)
                                                       (aget val (bit-xor l 1)) open
                                                       (= 1 (count open)) (reduced (conj open l))
                                                       :else (conj open l)))
                                               [] c)]
                              (cond (identical? :sat open) nil
                                    (empty? open) (do (vreset! conflict true) (reduced nil))
                                    (empty? (rest open)) (do (assign! (first open))
                                                             (when @conflict (reduced nil)))
                                    :else nil)))
                          nil (or (aget occ f) []))
                  (recur (inc qi)))))))
      (finally
        (doseq [l @trail] (aset val l nil))))))

(defn- rup!
  "With every literal of c false, unit propagation over the clauses of db
  falsifies one of them."
  [db c]
  (or (propagates-to-conflict? db (mapv #(bit-xor ((:ids db) %) 1) c))
      (reject! "the lemma " (pr-str c) " does not follow by unit propagation")))

(defn- lemma!
  "Lemma c follows from the clauses of db by its justification j."
  [db c j]
  (when-not (and (vector? c) (every? literal! c))
    (reject! "not a clause: " (pr-str c)))
  (cond
    (:rup j) (rup! db c)
    (contains? j :farkas)
    (let [ls (map first (:farkas j))]
      (when-not (= (set c) (set (map pre/negate ls)))
        (reject! "a Farkas lemma is not the negations of what it combines: " (pr-str c)))
      (farkas! (set ls) (:farkas j)))
    (contains? j :cut)
    (let [ls (map first (:cut j))
          m (:lit j)]
      (when-not (= (set c) (conj (set (map pre/negate ls)) m))
        (reject! "a cut lemma is not its cut and the negations of what it combines: " (pr-str c)))
      (when-not (= m (cut (set ls) (:cut j)))
        (reject! "a cut lemma's literal is not the cut: " (pr-str m))))
    :else (reject! "a lemma needs a justification: " (pr-str j))))

(defn- lemmas!
  "Each lemma follows from the clauses before it, and the last is empty."
  [clauses ls]
  (when-not (and (sequential? ls) (seq ls) (= [] (first (last ls))))
    (reject! "a lemma list must end with the empty clause"))
  (doseq [l ls]
    (let [c (when (and (vector? l) (= 2 (count l))) (first l))]
      (when-not (and (vector? c) (every? literal! c))
        (reject! "not a clause: " (pr-str c)))))
  (let [db (reduce add! (database (numbering (concat clauses (map first ls)))) clauses)]
    (reduce (fn [db [c j]] (lemma! db c j) (add! db c)) db ls)))

(defn verify
  "True when certificate c proves its claim of formula f under decls;
  otherwise throws, saying which step is wrong."
  [f decls c]
  (let [target (case (:claim c)
                 :unsat f
                 :valid [:not f]
                 (reject! "a certificate claims :unsat or :valid, not " (pr-str (:claim c))))]
    (let [clauses (if (contains? c :congruence)
                    ;; congruence added on demand: the formula's clauses,
                    ;; then each listed pair's constraint, in order
                    (let [{:keys [clauses apps]} (pre/preprocess target decls {:congruence false})
                          apps (vec apps)]
                      (into clauses (mapcat (fn [pr]
                                              (let [[i j] (when (and (vector? pr) (= 2 (count pr))) pr)]
                                                (when-not (and (integer? i) (integer? j) (< -1 i (count apps)) (< -1 j (count apps)))
                                                  (reject! "no pair of applications " (pr-str pr)))
                                                (pre/congruence-clauses (apps i) (apps j))))
                                            (:congruence c))))
                    (:clauses (pre/preprocess target decls)))
          p (:proof c)]
      (if (and (map? p) (contains? p :lemmas))
        (lemmas! clauses (:lemmas p))
        (check! clauses #{} p)))
    true))
