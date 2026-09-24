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

(defn- clause-state
  "What clause c says under assign: :sat, [:conflict], [:unit l] or nil."
  [c assign]
  (when-not (some assign c)
    (let [open (remove #(assign (negate %)) c)]
      (cond (empty? open) [:conflict]
            (empty? (rest open)) [:unit (first open)]))))

(defn- propagate
  "Unit propagation: [assign units conflict], units being [literal
  clause-index] in order.  Only the clauses that hold the negation of a
  literal just made true can have become unit or false, so those are the
  ones looked at: queue holds the literals made true since the last
  fixpoint, or is nil to look at every clause."
  [st assign queue]
  (let [clauses (:clauses @st)
        occ (:occ @st)
        look (fn [assign units is]
               (reduce (fn [[assign units q] i]
                         (let [r (clause-state (clauses i) assign)]
                           (case (first r)
                             :conflict (reduced [assign units q i])
                             :unit (if (assign (second r))
                                     [assign units q]
                                     [(conj assign (second r)) (conj units [(second r) i]) (conj q (second r))])
                             [assign units q])))
                       [assign units []] is))]
    (loop [assign assign, units [], queue (if (nil? queue) nil (vec queue)), first-pass (nil? queue)]
      (let [is (if first-pass
                 (range (count clauses))
                 (distinct (mapcat #(get occ (negate %)) queue)))
            [assign units q conflict] (look assign units is)]
        (cond
          conflict [assign units conflict]
          (seq q) (recur assign units q false)
          :else [assign units nil])))))

(defn- theory
  "The simplex on lits, started from the tableau the parent node ended
  with: a child adds a bound or two, so few pivots repair it."
  [st lits from]
  (or (get-in @st [:theory lits])
      (let [r (simplex/check lits (:max-pivots @st) from)]
        (vswap! st assoc-in [:theory lits] r)
        r)))

(declare node)

(defn- split
  "Try l, then its negation."
  [st assign cuts l tab]
  (budget! st)
  (let [neg (negate l)
        a (node st (conj assign l) cuts [l] tab)]
    (cond
      (:sat a) a
      (not ((:used a) l)) a
      :else (let [b (node st (conj assign neg) cuts [neg] tab)]
              (cond
                (:sat b) b
                (not ((:used b) neg)) b
                :else {:proof {:split l :yes (:proof a) :no (:proof b)}
                       :used (into (disj (:used a) l) (disj (:used b) neg))})))))

(defn- add-cut
  "Go on with the literal the cut terms derive."
  [st assign cuts terms tab]
  (budget! st)
  (let [l (cert/cut assign terms)
        r (node st (conj assign l) (inc cuts) [l] tab)]
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

(defn- node [st assign cuts fresh tab]
  (let [clauses (:clauses @st)
        [assign units conflict] (propagate st assign fresh)]
    (wrap-units
     st units
     (if conflict
       {:proof {:clause conflict} :used (set (map negate (clauses conflict)))}
       (let [lits (set (filter #(= :le (first %)) assign))
             t (theory st lits tab)
             tab (or (:tableau t) tab)]
         (if-let [fk (:conflict t)]
           (let [fk (vec (remove #(zero? (second %)) fk))]
             {:proof {:farkas fk} :used (set (map first fk))})
           (if-let [c (first (remove #(some assign %) clauses))]
             (split st assign cuts (first (remove #(assign (negate %)) c)) tab)
             (if-let [[x v] (first (remove #(integer? (val %)) (sort-by (comp str key) (:sat t))))]
               (let [terms (when (< cuts max-cuts) (simplex/gomory (:tableau t)))]
                 (if (and terms (not (assign (cert/cut assign terms))))
                   (add-cut st assign cuts terms tab)
                   (split st assign cuts [:le {x 1} (simplex/floor-value v)] tab)))
               {:sat true :assign assign :values (:sat t)}))))))))

(defn solve
  "Search clauses for a model.  {:sat true :assign #{literal} :values
  {var int}} or {:proof p}; throws ::budget when out of decisions."
  [clauses {:keys [budget max-pivots]}]
  (let [occ (reduce (fn [m [i c]] (reduce (fn [m l] (update m l (fnil conj []) i)) m c))
                    {} (map-indexed vector clauses))
        st (volatile! {:clauses clauses :budget budget :max-pivots max-pivots
                       :decisions 0 :theory {} :occ occ})]
    (node st #{} 0 nil nil)))
