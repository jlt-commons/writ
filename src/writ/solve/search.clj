(ns writ.solve.search
  "The search for a model of a set of clauses over linear literals: DPLL
  with unit propagation, the simplex as its theory solver, and
  branch-and-bound for integrality.  None of it is trusted: an unsat
  answer comes with a proof that writ.solve.cert checks on its own.

  The proof is the search tree.  Each node splits on a literal, one that
  was decided, propagated, or a branch-and-bound cut x <= k, or adds a
  Gomory cut, which is a Chvatal-Gomory combination of literals on the
  branch; each leaf
  names what closes its branch: a clause every literal of which is false
  there, or a Farkas combination of the inequalities that hold there.
  A subtree that never used its branch's literal proves its goal without
  it, and replaces the split: backjumping, and a smaller proof."
  (:require [writ.solve.pre :refer [negate]]
            [writ.solve.simplex :as simplex]
            [writ.solve.cert :as cert]))

(def max-cuts
  "The most Gomory cuts on one branch before branch-and-bound takes over."
  12)

(defn- budget! [st]
  (vswap! st update :decisions inc)
  (when (> (:decisions @st) (:budget @st))
    (throw (ex-info (str "the budget of " (:budget @st) " decisions is exhausted") {::budget true}))))

(defn- propagate
  "Unit propagation from the true literals in assign: [assign units
  conflict], units being [literal clause-index] in order."
  [clauses assign]
  (loop [assign assign units []]
    (let [step (reduce (fn [_ i]
                         (let [c (clauses i)]
                           (when-not (some assign c)
                             (let [open (remove #(assign (negate %)) c)]
                               (cond (empty? open) (reduced [:conflict i])
                                     (empty? (rest open)) (reduced [:unit (first open) i]))))))
                       nil (range (count clauses)))]
      (case (first step)
        :conflict [assign units (second step)]
        :unit (recur (conj assign (second step)) (conj units (vec (rest step))))
        [assign units nil]))))

(defn- theory [st lits]
  (or (get-in @st [:theory lits])
      (let [r (simplex/check lits (:max-pivots @st))]
        (vswap! st assoc-in [:theory lits] r)
        r)))

(declare node)

(defn- split
  "Try l, then its negation."
  [st assign cuts l]
  (budget! st)
  (let [neg (negate l)
        a (node st (conj assign l) cuts)]
    (cond
      (:sat a) a
      (not ((:used a) l)) a
      :else (let [b (node st (conj assign neg) cuts)]
              (cond
                (:sat b) b
                (not ((:used b) neg)) b
                :else {:proof {:split l :yes (:proof a) :no (:proof b)}
                       :used (into (disj (:used a) l) (disj (:used b) neg))})))))

(defn- add-cut
  "Go on with the literal the cut terms derive."
  [st assign cuts terms]
  (budget! st)
  (let [l (cert/cut assign terms)
        r (node st (conj assign l) (inc cuts))]
    (if (or (:sat r) (not ((:used r) l)))
      r
      {:proof {:cut terms :then (:proof r)}
       :used (into (disj (:used r) l) (map first terms))})))

(defn- wrap-units
  "Put the propagated literals back into the proof, as splits whose other
  branch the propagating clause closes."
  [st units r]
  (let [clauses (:clauses @st)]
    (reduce (fn [r [l i]]
              (if (or (:sat r) (not ((:used r) l)))
                r
                {:proof {:split l :yes (:proof r) :no {:clause i}}
                 :used (into (disj (:used r) l)
                             (disj (set (map negate (clauses i))) (negate l)))}))
            r (reverse units))))

(defn- node [st assign cuts]
  (let [clauses (:clauses @st)
        [assign units conflict] (propagate clauses assign)]
    (wrap-units
     st units
     (if conflict
       {:proof {:clause conflict} :used (set (map negate (clauses conflict)))}
       (let [lits (set (filter #(= :le (first %)) assign))
             t (theory st lits)]
         (if-let [fk (:conflict t)]
           (let [fk (vec (remove #(zero? (second %)) fk))]
             {:proof {:farkas fk} :used (set (map first fk))})
           (if-let [c (first (remove #(some assign %) clauses))]
             (split st assign cuts (first (remove #(assign (negate %)) c)))
             (if-let [[x v] (first (remove #(integer? (val %)) (sort-by (comp str key) (:sat t))))]
               (let [terms (when (< cuts max-cuts) (simplex/gomory (:tableau t)))]
                 (if (and terms (not (assign (cert/cut assign terms))))
                   (add-cut st assign cuts terms)
                   (split st assign cuts [:le {x 1} (simplex/floor-value v)])))
               {:sat true :assign assign :values (:sat t)}))))))))

(defn solve
  "Search clauses for a model.  {:sat true :assign #{literal} :values
  {var int}} or {:proof p}; throws ::budget when out of decisions."
  [clauses {:keys [budget max-pivots]}]
  (let [st (volatile! {:clauses clauses :budget budget :max-pivots max-pivots
                       :decisions 0 :theory {}})]
    (node st #{} 0)))
