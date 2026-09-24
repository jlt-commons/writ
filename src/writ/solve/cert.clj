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

(defn verify
  "True when certificate c proves its claim of formula f under decls;
  otherwise throws, saying which step is wrong."
  [f decls c]
  (let [target (case (:claim c)
                 :unsat f
                 :valid [:not f]
                 (reject! "a certificate claims :unsat or :valid, not " (pr-str (:claim c))))]
    (check! (:clauses (pre/preprocess target decls)) #{} (:proof c))
    true))
