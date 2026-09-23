(ns writ.solve.pre
  "The solver's formulas brought to clauses of linear literals.

  A formula over integers is rewritten, deterministically, into a set of
  clauses whose literals are of two kinds:

    [:le {x a, y b ...} c]   a*x + b*y + ... <= c, integers throughout
    [:bool v true|false]     a boolean variable, or its negation

  Every term is first made linear, a map of variables to coefficients and
  a constant.  The rest are named by fresh variables, defined by side
  constraints that are conjoined with the formula:

  * (mod t k) and (quot t k) name a quotient q and remainder r with
    t = k*q + r, and r bounded as clojure.core has it: mod takes the sign
    of the divisor, quot truncates toward zero
  * abs, max, min and ite name their value, with one case per branch
  * each distinct application of an uninterpreted fn or predicate, its
    arguments made linear, is a fresh variable; for each pair of
    applications of the same fn, equal arguments imply equal results
    (Ackermann's reduction)

  Each fresh variable is defined as a total function of the others, so any
  model of the formula extends to one of the result: when the clauses have
  no model, neither has the formula.  A literal's negation is again a
  literal, since over the integers not (a.x <= c) is (-a).x <= -c - 1, and
  an inequality is divided through by its coefficients' gcd, rounding the
  bound down, which is exact over the integers.

  The boolean structure goes to clauses by Tseitin's encoding in the
  one-directional form of Plaisted and Greenbaum, again adding only
  definitions.  Both the search and the certificate checker run this
  namespace, so a certificate is always checked against the clauses the
  checker made itself.")

(defn unsupported! [msg t]
  (throw (ex-info msg {:writ.solve/unsupported t})))

;; --- linear terms: [{var coeff} constant] -------------------------------------

(defn- lin-add [[a c] [b d]]
  [(reduce-kv (fn [m x k] (let [s (+ (get m x 0) k)] (if (zero? s) (dissoc m x) (assoc m x s))))
              a b)
   (+ c d)])

(defn- lin-scale [k [a c]]
  (if (zero? k) [{} 0] [(into {} (map (fn [[x v]] [x (* k v)])) a) (* k c)]))

(defn- lin-sub [l m] (lin-add l (lin-scale -1 m)))

(defn- constant? [[a _]] (empty? a))

(defn lin-value
  "The value of a linear term under an assignment of its variables."
  [[a c] value-of]
  (reduce-kv (fn [s x k] (+ s (* k (value-of x)))) c a))

;; --- literals ------------------------------------------------------------------

(defn- gcd [a b] (if (zero? b) (abs a) (recur b (rem a b))))

(defn- floor-div [a g] (quot (- a (mod a g)) g))

(defn le
  "The literal for l <= 0, or true or false when l is a constant."
  [[a c]]
  (if (empty? a)
    (<= c 0)
    (let [g (reduce gcd 0 (vals a))]
      [:le (into {} (map (fn [[x k]] [x (quot k g)])) a) (floor-div (- c) g)])))

(defn negate
  "A literal's negation."
  [[kind x y]]
  (case kind
    :le [:le (into {} (map (fn [[v k]] [v (- k)])) x) (- (- y) 1)]
    :bool [:bool x (not y)]))

(defn literal? [f] (contains? #{:le :bool} (and (vector? f) (first f))))

;; --- formulas in negation normal form: true, false, literals, :and, :or ----------

(defn- conj* [fs]
  (let [fs (mapcat (fn [f] (if (and (vector? f) (= :and (first f))) (rest f) [f])) fs)]
    (cond (some false? fs) false
          :else (let [fs (vec (distinct (remove true? fs)))]
                  (case (count fs) 0 true 1 (first fs) (into [:and] fs))))))

(defn- disj* [fs]
  (let [fs (mapcat (fn [f] (if (and (vector? f) (= :or (first f))) (rest f) [f])) fs)]
    (cond (some true? fs) true
          :else (let [fs (vec (distinct (remove false? fs)))]
                  (case (count fs) 0 false 1 (first fs) (into [:or] fs))))))

(defn- negf [f]
  (cond (true? f) false
        (false? f) true
        (literal? f) (negate f)
        (= :and (first f)) (disj* (map negf (rest f)))
        :else (conj* (map negf (rest f)))))

(defn- le* [l m] (le (lin-sub l m)))
(defn- lt* [l m] (le (lin-add (lin-sub l m) [{} 1])))
(defn- eq* [l m] (conj* [(le* l m) (le* m l)]))

;; --- translation ---------------------------------------------------------------

(defn- fresh!
  "The fresh variable memoised under key, defining it by (side v) when new."
  [st key side]
  (or (get-in @st [:memo key])
      (let [v [:% (:n @st)]]
        (vswap! st #(-> % (update :n inc) (assoc-in [:memo key] v)))
        (vswap! st update :sides conj (side v))
        v)))

(defn- fresh-app!
  "The variable for the application of f to linear args ls."
  [st kind f ls]
  (or (get-in @st [:memo [kind f ls]])
      (let [v [:% (:n @st)]]
        (vswap! st #(-> % (update :n inc) (assoc-in [:memo [kind f ls]] v)
                        (update :apps conj {:kind kind :f f :args ls :var v})))
        v)))

(defn- check-arity [decls f kind n t]
  (when-let [d (get decls f)]
    (when-not (and (vector? d) (= kind (first d)) (= n (second d)))
      (unsupported! (str "`" f "` is declared " (pr-str d)) t))))

(declare formula)

(defn- term
  "The linear form of an integer term."
  [st decls t]
  (let [tm #(term st decls %)
        v [{} 0]]
    (cond
      (integer? t) [{} t]
      (symbol? t) (if (= :bool (get decls t))
                    (unsupported! (str "`" t "` is a boolean, not an integer") t)
                    [{t 1} 0])
      (not (vector? t)) (unsupported! (str "not an integer term: " (pr-str t)) t)
      :else
      (let [[op & args] t]
        (case op
          :+ (reduce lin-add v (map tm args))
          :- (if (= 1 (count args))
               (lin-scale -1 (tm (first args)))
               (reduce lin-sub (map tm args)))
          :neg (lin-scale -1 (tm (first args)))
          :* (let [ls (map tm args)
                   vs (remove constant? ls)]
               (when (next vs) (unsupported! "a product of variables is not linear" t))
               (lin-scale (reduce * 1 (map second (filter constant? ls)))
                          (or (first vs) [{} 1])))
          (:mod :quot)
          (let [[x k] args
                l (tm x)]
            (when-not (and (integer? k) (not (zero? k)))
              (unsupported! "a divisor must be a nonzero integer literal" t))
            (if (constant? l)
              [{} ((if (= op :mod) mod quot) (second l) k)]
              (let [q (fresh! st [:q op l k] (fn [_] true))
                    r (fresh! st [op l k]
                              (fn [r]
                                (let [q [{q 1} 0] r [{r 1} 0] m (dec (abs k))]
                                  (conj* [(eq* l (lin-add (lin-scale k q) r))
                                          (le* r [{} m]) (le* [{} (- m)] r)
                                          (if (= op :mod)
                                            (if (pos? k) (le* [{} 0] r) (le* r [{} 0]))
                                            (conj* [(disj* [(lt* l [{} 0]) (le* [{} 0] r)])
                                                    (disj* [(le* [{} 0] l) (le* r [{} 0])])]))]))))]
                [{(if (= op :mod) r q) 1} 0])))
          :abs (let [l (tm (first args))]
                 (if (constant? l)
                   [{} (abs (second l))]
                   [{(fresh! st [:abs l]
                             (fn [a] (let [a [{a 1} 0]]
                                       (conj* [(disj* [(lt* l [{} 0]) (eq* a l)])
                                               (disj* [(le* [{} 0] l) (eq* a (lin-scale -1 l))])]))))
                     1} 0]))
          (:max :min)
          (let [[l m] (map tm args)
                pick (if (= op :max) max min)]
            (when-not (= 2 (count args)) (unsupported! "max and min take two terms" t))
            (if (and (constant? l) (constant? m))
              [{} (pick (second l) (second m))]
              ;; max is l when m <= l; min is l when l <= m
              (let [l-wins (if (= op :max) (le* m l) (le* l m))]
                [{(fresh! st [op l m]
                          (fn [a] (let [a [{a 1} 0]]
                                    (conj* [(disj* [(negf l-wins) (eq* a l)])
                                            (disj* [l-wins (eq* a m)])]))))
                  1} 0])))
          :ite (let [[b x y] args
                     c (formula st decls b)
                     l (tm x)
                     m (tm y)]
                 (cond (true? c) l
                       (false? c) m
                       (= l m) l
                       :else [{(fresh! st [:ite c l m]
                                       (fn [a] (let [a [{a 1} 0]]
                                                 (conj* [(disj* [(negf c) (eq* a l)])
                                                         (disj* [c (eq* a m)])]))))
                               1} 0]))
          :app (let [[f & xs] args]
                 (check-arity decls f :fn (count xs) t)
                 [{(fresh-app! st :fn f (mapv tm xs)) 1} 0])
          (unsupported! (str "not an integer term: " (pr-str t)) t))))))

(defn- chain
  "A comparison of each adjacent pair of terms, as clojure.core's are."
  [st decls rel ts]
  (let [ls (map #(term st decls %) ts)]
    (conj* (map rel ls (rest ls)))))

(defn- formula
  "The negation normal form of a formula."
  [st decls f]
  (let [fm #(formula st decls %)]
    (cond
      (boolean? f) f
      (symbol? f) (if (contains? #{nil :bool} (get decls f))
                    [:bool f true]
                    (unsupported! (str "`" f "` is not a boolean") f))
      (not (vector? f)) (unsupported! (str "not a formula: " (pr-str f)) f)
      :else
      (let [[op & args] f]
        (case op
          :and (conj* (map fm args))
          :or (disj* (map fm args))
          :not (negf (fm (first args)))
          :=> (disj* [(negf (fm (first args))) (fm (second args))])
          :iff (let [[p q] (map fm args)]
                 (conj* [(disj* [(negf p) q]) (disj* [p (negf q)])]))
          := (chain st decls eq* args)
          :< (chain st decls lt* args)
          :<= (chain st decls le* args)
          :> (chain st decls #(lt* %2 %1) args)
          :>= (chain st decls #(le* %2 %1) args)
          :distinct (let [ls (vec (map #(term st decls %) args))]
                      (conj* (for [i (range (count ls)) j (range (inc i) (count ls))]
                               (negf (eq* (ls i) (ls j))))))
          :papp (let [[p & xs] args]
                  (check-arity decls p :pred (count xs) f)
                  [:bool (fresh-app! st :pred p (mapv #(term st decls %) xs)) true])
          (unsupported! (str "not a formula: " (pr-str f)) f))))))

(defn- ackermann
  "For each pair of applications of one fn: equal arguments, equal results."
  [apps]
  (conj* (for [[i a] (map-indexed vector apps)
               b (drop (inc i) apps)
               :when (and (= (:kind a) (:kind b)) (= (:f a) (:f b)))]
           (disj* (concat (map (comp negf eq*) (:args a) (:args b))
                          [(if (= :fn (:kind a))
                             (eq* [{(:var a) 1} 0] [{(:var b) 1} 0])
                             (let [p [:bool (:var a) true] q [:bool (:var b) true]]
                               (conj* [(disj* [(negate p) q]) (disj* [p (negate q)])])))])))))

;; --- clauses -------------------------------------------------------------------

(defn- name-of!
  "A literal standing for f: f itself, or a fresh variable implying it."
  [st f]
  (if (literal? f)
    f
    (let [p [:bool [:t (:n @st)] true]]
      (vswap! st update :n inc)
      (let [names (mapv #(name-of! st %) (rest f))]
        (vswap! st update :clauses into
                (if (= :and (first f))
                  (map (fn [g] [(negate p) g]) names)
                  [(into [(negate p)] names)])))
      p)))

(defn- clausify! [st f]
  (cond
    (true? f) nil
    (false? f) (vswap! st update :clauses conj [])
    (literal? f) (vswap! st update :clauses conj [f])
    (= :and (first f)) (doseq [g (rest f)] (clausify! st g))
    :else (let [c (mapv #(name-of! st %) (rest f))]
            (vswap! st update :clauses conj c))))

(defn preprocess
  "The clauses of formula under decls, with the applications they name:
  {:clauses [[lit ...] ...] :apps [{:kind :f :args :var} ...]}."
  [f decls]
  (let [st (volatile! {:n 0 :memo {} :sides [] :apps [] :clauses []})
        main (formula st decls f)
        whole (conj* (concat [main] (:sides @st) [(ackermann (:apps @st))]))]
    (clausify! st whole)
    (select-keys @st [:clauses :apps])))
