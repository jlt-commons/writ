(ns writ.solve.simplex
  "Feasibility of linear inequalities over the rationals, by the general
  simplex of Dutertre and de Moura.

  Each inequality a.x <= c bounds a variable: x itself when a is a single
  unit coefficient, otherwise a slack s = a.x, one per distinct form up to
  sign.  The tableau keeps the basic variables as linear combinations of
  the nonbasic ones; nonbasic variables always sit within their bounds,
  and a basic variable out of its bounds is pivoted back, choosing
  variables by Bland's rule so the search ends.

  When a basic variable cannot be brought back, its row names the bounds
  that stop it, and those bounds, weighted by the row's coefficients, sum
  to 0 <= a negative constant: a Farkas certificate over the literals the
  bounds came from.  Everything is exact: Clojure's ratios.")

(defn- floor-rat [v]
  (if (integer? v) v (let [n (numerator v) d (denominator v)] (quot (- n (mod n d)) d))))

(defn floor-value [v] (floor-rat v))

(defn- neg-form [a] (into {} (map (fn [[x k]] [x (- k)])) a))

(defn- bound-of
  "The variable a literal bounds, the side, and the bound's value."
  [slacks [_ a c]]
  (if (and (= 1 (count a)) (#{1 -1} (val (first a))))
    (let [[x k] (first a)] (if (= 1 k) [x :hi c] [x :lo (- c)]))
    (if (contains? slacks (neg-form a))
      [[:slack (neg-form a)] :lo (- c)]
      [[:slack a] :hi c])))

(defn- tighter? [side v old] (or (nil? old) (if (= side :hi) (< v (first old)) (> v (first old)))))

(defn- value [st x] (get-in st [:val x] 0))

(defn- violation [st x]
  (let [v (value st x) lo (get-in st [:bounds x :lo]) hi (get-in st [:bounds x :hi])]
    (cond (and lo (< v (first lo))) :lo
          (and hi (> v (first hi))) :hi)))

(defn- pivot-and-update
  "Set basic xi to v by moving nonbasic xj, then swap their roles."
  [st xi xj v]
  (let [rows (:rows st)
        row (rows xi)
        a (row xj)
        theta (/ (- v (value st xi)) a)
        vals (reduce-kv (fn [m k r] (if-let [c (r xj)] (assoc m k (+ (get m k 0) (* c theta))) m))
                        (:val st) (dissoc rows xi))
        vals (-> vals (assoc xi v) (assoc xj (+ (value st xj) theta)))
        new-row (reduce-kv (fn [m k c] (if (= k xj) m (assoc m k (- (/ c a))))) {xi (/ 1 a)} row)
        subst (fn [r] (if-let [c (r xj)]
                        (reduce-kv (fn [m k d] (let [s (+ (get m k 0) (* c d))]
                                                 (if (zero? s) (dissoc m k) (assoc m k s))))
                                   (dissoc r xj) new-row)
                        r))
        rows (-> (into {} (map (fn [[k r]] [k (subst r)])) (dissoc rows xi))
                 (assoc xj new-row))]
    (assoc st :rows rows :val vals)))

(defn- explain
  "The Farkas multipliers for basic x stuck below (side :lo) or above its bound."
  [st x side]
  (let [other {:lo :hi :hi :lo}
        lit (fn [y s] (second (get-in st [:bounds y s])))]
    (into [[(lit x side) 1]]
          (for [[y a] (get-in st [:rows x])]
            (if (pos? a)
              [(lit y (other side)) a]
              [(lit y side) (- a)])))))

(defn- register [st x]
  (if (contains? (:idx st) x) st (assoc-in st [:idx x] (count (:idx st)))))

(defn- row-of
  "Linear form a written over the nonbasic variables of the tableau."
  [st a]
  (reduce-kv (fn [m y k]
               (if-let [r (get-in st [:rows y])]
                 (reduce-kv (fn [m z d] (let [v (+ (get m z 0) (* k d))] (if (zero? v) (dissoc m z) (assoc m z v))))
                            m r)
                 (let [v (+ (get m y 0) k)] (if (zero? v) (dissoc m y) (assoc m y v)))))
             {} a))

(defn- assert-lit
  "The tableau with literal l's bound added: a new variable is nonbasic at
  0, a new slack a basic row over the nonbasic variables."
  [st [_ a _ :as l]]
  (let [multi (not (and (= 1 (count a)) (#{1 -1} (val (first a)))))
        st (reduce register st (keys a))
        st (if (and multi (not (contains? (:slacks st) a)) (not (contains? (:slacks st) (neg-form a))))
             (let [sx [:slack a]
                   row (row-of st a)]
               (-> st (update :slacks conj a) (assoc-in [:rows sx] row)
                   (register sx)
                   (assoc-in [:val sx] (reduce-kv (fn [t x k] (+ t (* k (get-in st [:val x] 0)))) 0 row))))
             st)
        [x side v] (bound-of (:slacks st) l)
        st (register st x)]
    (if (tighter? side v (get-in st [:bounds x side]))
      (assoc-in st [:bounds x side] [v l])
      st)))

(defn- repair-nonbasic
  "Move each nonbasic variable out of bounds to the bound it breaks, and
  the basic variables with it."
  [st]
  (reduce (fn [st x]
            (if (contains? (:rows st) x)
              st
              (let [v (value st x)
                    {:keys [lo hi]} (get-in st [:bounds x])
                    target (cond (and lo (< v (first lo))) (first lo)
                                 (and hi (> v (first hi))) (first hi))]
                (if (nil? target)
                  st
                  (let [d (- target v)]
                    (reduce-kv (fn [st b r] (if-let [c (r x)] (update-in st [:val b] (fnil + 0) (* c d)) st))
                               (assoc-in st [:val x] target) (:rows st)))))))
          st (keys (:idx st))))

(defn empty-tableau []
  {:slacks #{} :rows {} :bounds {} :idx {} :val {}})

(defn check
  "Are the literals [:le a c] satisfiable over the rationals?  {:sat
  values :tableau t} or {:conflict [[literal multiplier] ...]}.  Throws
  ::budget after max-pivots pivots.  Given a tableau a check of fewer of
  the literals ended with, it starts from there: only the new bounds need
  repairing."
  ([lits max-pivots] (check lits max-pivots nil))
  ([lits max-pivots from]
   (let [base (or from (empty-tableau))
         st (reduce assert-lit base (remove (or (:asserted base) #{}) lits))
         st (assoc st :asserted (into (or (:asserted base) #{}) lits))
         clash (some (fn [[x {:keys [lo hi]}]] (when (and lo hi (> (first lo) (first hi))) x))
                     (:bounds st))]
     (if clash
       {:conflict [[(second (get-in st [:bounds clash :lo])) 1]
                   [(second (get-in st [:bounds clash :hi])) 1]]}
       (let [order #(get-in st [:idx %])]
         (loop [st (repair-nonbasic st) n 0]
          (when (> n max-pivots)
            (throw (ex-info "simplex pivot budget exhausted" {::budget true})))
          (let [bad (first (sort-by order (filter #(violation st %) (keys (:rows st)))))]
            (if-not bad
              {:sat (into {} (for [x (keys (:idx st)) :when (not (and (vector? x) (= :slack (first x))))]
                               [x (value st x)]))
               :tableau st}
              (let [side (violation st bad)
                    target (first (get-in st [:bounds bad side]))
                    ;; below its lower bound it must rise, above its upper it must fall
                    can? (fn [[y a]]
                           (let [up (if (= side :lo) (pos? a) (neg? a))
                                 b (get-in st [:bounds y (if up :hi :lo)])]
                             (or (nil? b) (if up (< (value st y) (first b)) (> (value st y) (first b))))))
                    y (first (sort-by order (map first (filter can? (get-in st [:rows bad])))))]
                (if y
                  (recur (pivot-and-update st bad y target) (inc n))
                  {:conflict (explain st bad side)}))))))))))

(defn gomory
  "A Gomory cut for a satisfied tableau whose basic variable x has a
  fractional value and a row of nonbasic variables all at a bound, as the
  Chvatal-Gomory multipliers [[literal k] ...] that derive it, or nil.

  Write each nonbasic y as its bound plus or minus a slack s >= 0, so
  x = v + sum a's; the literals saying s >= 0, weighted by the fractional
  parts of a', sum to an inequality with integer coefficients that the
  current point violates once its bound is rounded down."
  [{:keys [rows bounds val idx]}]
  (let [value #(get val % 0)
        frac #(- % (floor-rat %))]
    (first
     (for [[x row] (sort-by (comp idx key) rows)
           :when (not (integer? (value x)))
           :let [terms (for [[y a] row]
                         (let [{:keys [lo hi]} (get bounds y)]
                           (cond (and lo (= (value y) (first lo))) [(second lo) (frac a)]
                                 (and hi (= (value y) (first hi))) [(second hi) (frac (- a))])))]
           :when (every? some? terms)
           :let [terms (vec (remove (comp zero? second) terms))]
           :when (seq terms)]
       terms))))
