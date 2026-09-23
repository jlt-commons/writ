(ns writ.solve
  "A certifying solver for linear integer arithmetic with uninterpreted
  functions, quantifier free.

  A formula is plain data:

    terms     integers, symbols, [:+ t ...] [:- t u ...] [:neg t]
              [:* k t] (k an integer), [:mod t k] [:quot t k] (as in
              clojure.core, k a nonzero integer), [:abs t] [:max t u]
              [:min t u] [:ite p t u], [:app f t ...]
    formulas  true false, boolean symbols, [:and p ...] [:or p ...]
              [:not p] [:=> p q] [:iff p q], [:= t u ...] [:distinct t ...]
              [:< t u ...] [:<= t u ...] [:> t u ...] [:>= t u ...],
              [:papp p t ...]

  with declarations {x :int, b :bool, f [:fn 2], p [:pred 1]}; an
  undeclared symbol is an integer in a term and a boolean in a formula.

  `check` answers :sat with a model, :unsat with a certificate, or
  :unknown when its budget runs out.  The search that finds either is
  not trusted: `verify` checks a certificate without it, with only
  writ.solve.pre and writ.solve.cert, and a model is checked by `eval-formula`."
  (:require [writ.solve.pre :as pre]
            [writ.solve.search :as search]
            [writ.solve.simplex :as simplex]
            [writ.solve.cert :as cert]))

(def default-budget 20000)

(defn- model
  "The values of the formula's own variables, and a finite map with a
  default for each of its fns and predicates."
  [f decls apps {:keys [assign values]}]
  (let [value-of #(get values % 0)
        empty-fn (fn [kind] {:map {} :default (if (= :fn kind) 0 false)})
        declared (into {} (for [[g d] decls :when (vector? d)] [g (empty-fn (first d))]))
        fns (reduce (fn [m {:keys [kind f args var]}]
                      (update m f (fn [i] (assoc-in (or i (empty-fn kind))
                                                    [:map (mapv #(pre/lin-value % value-of) args)]
                                                    (if (= :fn kind)
                                                      (value-of var)
                                                      (contains? assign [:bool var true]))))))
                    declared apps)
        bool? (fn [x] (or (= :bool (get decls x))
                          (contains? assign [:bool x true]) (contains? assign [:bool x false])))]
    (into fns
          (for [x (into #{} (filter symbol?) (tree-seq vector? seq f))
                :when (not (contains? fns x))]
            [x (if (bool? x) (contains? assign [:bool x true]) (value-of x))]))))

(defn check
  "Is formula f satisfiable?  {:result :sat :model m}, {:result :unsat
  :certificate c} or {:result :unknown :reason s}.  opts: :budget, the
  most decisions and branch-and-bound splits to make."
  [f decls opts]
  (let [{:keys [clauses apps]} (pre/preprocess f decls)
        budget (or (:budget opts) default-budget)]
    (try
      (let [r (search/solve clauses {:budget budget :max-pivots (* 100 (max budget 100))})]
        (if (:sat r)
          {:result :sat :model (model f decls apps r)}
          {:result :unsat :certificate {:claim :unsat :proof (:proof r)}}))
      (catch clojure.lang.ExceptionInfo e
        (if (or (::search/budget (ex-data e)) (::simplex/budget (ex-data e)))
          {:result :unknown :reason (ex-message e)}
          (throw e))))))

(defn valid?
  "Is formula f true in every model?  {:result :valid :certificate c},
  {:result :invalid :model m} (a counter-model) or {:result :unknown}."
  [f decls opts]
  (let [r (check [:not f] decls opts)]
    (case (:result r)
      :unsat {:result :valid :certificate (assoc (:certificate r) :claim :valid)}
      :sat {:result :invalid :model (:model r)}
      r)))

(defn verify
  "True when certificate c proves what it claims of f: that f is
  unsatisfiable, or valid.  Throws ex-info naming the wrong step
  otherwise.  It runs no search."
  [f decls c]
  (cert/verify f decls c))

;; --- evaluation ----------------------------------------------------------------

(declare eval-formula)

(defn- eval-term [t m]
  (let [ev #(eval-term % m)]
    (cond
      (integer? t) t
      (symbol? t) (let [v (get m t 0)] (if (integer? v) v 0))
      :else
      (let [[op & args] t]
        (case op
          :+ (reduce + 0 (map ev args))
          :- (apply - (map ev args))
          :neg (- (ev (first args)))
          :* (reduce * 1 (map ev args))
          :mod (mod (ev (first args)) (second args))
          :quot (quot (ev (first args)) (second args))
          :abs (abs (ev (first args)))
          :max (max (ev (first args)) (ev (second args)))
          :min (min (ev (first args)) (ev (second args)))
          :ite (if (eval-formula (first args) m) (ev (second args)) (ev (nth args 2)))
          :app (let [{fm :map d :default} (get m (first args))]
                 (get fm (mapv ev (rest args)) (or d 0))))))))

(defn eval-formula
  "The truth of formula f in model m: a map of variables to values, and
  of fns and predicates to {:map {args value} :default value}."
  [f m]
  (let [ev #(eval-formula % m)
        terms #(map (fn [t] (eval-term t m)) %)]
    (cond
      (boolean? f) f
      (symbol? f) (true? (get m f))
      :else
      (let [[op & args] f]
        (case op
          :and (every? ev args)
          :or (boolean (some ev args))
          :not (not (ev (first args)))
          :=> (or (not (ev (first args))) (ev (second args)))
          :iff (= (ev (first args)) (ev (second args)))
          := (apply = (terms args))
          :distinct (apply distinct? (terms args))
          :< (apply < (terms args))
          :<= (apply <= (terms args))
          :> (apply > (terms args))
          :>= (apply >= (terms args))
          :papp (let [{pm :map d :default} (get m (first args))]
                  (true? (get pm (vec (terms (rest args))) (boolean d)))))))))
