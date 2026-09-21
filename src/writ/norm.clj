(ns writ.norm
  "Normalisation and convertibility for the core AST from writ.lower.

  Only reductions that are true of Clojure itself, under its strict
  evaluation: beta for a let or an applied fn whose argument is already a
  value (a term that could throw is never dropped or moved), `if` on a
  literal, `case` on a literal, clojure.core arithmetic and comparison on
  literals, dropping `do` statements that are values, and the identities
  (+ x 0) -> x and (* x 1) -> x when x is known to be a number.  A literal
  fold that throws, or a literal `case` with no matching clause, reduces to
  an error node: a term that throws is not equal to anything.

  Terms are uniquified before reduction, so substitution cannot capture,
  and compared up to alpha (binders renamed canonically)."
  (:require [writ.lower :as l]))

(def ^:dynamic *opaque*
  "Book names that shadow clojure.core: a call to one is the book's fn,
  never folded."
  #{})

(def ^:dynamic *numeric*
  "Variables known to be numbers (bound by a forall or exists over a
  numeric type): the identities fold only on these, number literals and
  arithmetic."
  #{})

(def ^:dynamic *numeric-fns*
  "Book fns declared to return a number: a call to one is a number (or
  throws, on both sides alike)."
  #{})

(defn- lit? [t] (and (map? t) (= :lit (:op t))))
(defn- lv [t] (:val t))
(defn- truthy? [v] (not (or (nil? v) (false? v))))

(declare subst)

(defn- shadow? [b name] (boolean (some #{name} (l/binding-names b))))

(defn- subst-bindings
  [bindings body name val]
  (loop [bs bindings, acc [], done false]
    (if (empty? bs)
      {:bindings (vec acc) :body (if done body (subst body name val))}
      (let [[b init] (first bs)
            init* (if done init (subst init name val))
            shadow (shadow? b name)]
        (recur (rest bs) (conj acc [b init*]) (or done shadow))))))

(defn subst
  "Replace free occurrences of `name` in AST with `val`, respecting binders.
  Callers uniquify first, so `val`'s free names are never rebound inside."
  [ast name val]
  (case (:op ast)
    :ref (if (= name (:name ast)) val ast)
    :lit ast
    :error ast
    :if (assoc ast :test (subst (:test ast) name val)
                   :then (subst (:then ast) name val)
                   :else (subst (:else ast) name val))
    :do (assoc ast :stmts (mapv #(subst % name val) (:stmts ast))
                   :ret (subst (:ret ast) name val))
    :invoke (assoc ast :fn (subst (:fn ast) name val)
                       :args (mapv #(subst % name val) (:args ast)))
    :recur (assoc ast :args (mapv #(subst % name val) (:args ast)))
    :fn (if (or (some #{name} (:params ast)) (= name (:name ast)))
          ast
          (assoc ast :body (subst (:body ast) name val)))
    :let (let [{:keys [bindings body]} (subst-bindings (:bindings ast) (:body ast) name val)]
           (assoc ast :bindings bindings :body body))
    :loop (let [{:keys [bindings body]} (subst-bindings (:bindings ast) (:body ast) name val)]
             (assoc ast :bindings bindings :body body))
    :case (assoc ast :scrut (subst (:scrut ast) name val)
                     :clauses (mapv (fn [c] (assoc c :body (subst (:body c) name val)))
                                    (:clauses ast))
                     :default (when (:default ast) (subst (:default ast) name val)))
    :vec (assoc ast :items (mapv #(subst % name val) (:items ast)))
    :set (assoc ast :items (mapv #(subst % name val) (:items ast)))
    :map (assoc ast :keys (mapv #(subst % name val) (:keys ast))
                    :vals (mapv #(subst % name val) (:vals ast)))
    ast))

(defn- value?
  "A term whose evaluation cannot throw or diverge: safe to substitute."
  [t]
  (case (:op t)
    (:lit :ref :fn) true
    (:vec :set) (every? value? (:items t))
    :map (and (every? value? (:keys t)) (every? value? (:vals t)))
    false))

(def ^:private builtins
  {'+ + '- - '* * 'inc inc 'dec dec 'quot quot 'rem rem 'mod mod
   'max max 'min min
   'zero? zero? 'pos? pos? 'neg? neg?
   '= = 'not= not= '< < '> > '<= <= '>= >=})

(def ^:private arithmetic '#{+ - * inc dec quot rem mod max min})

(defn- core-name
  "The clojure.core name a call head resolves to, or nil: a qualified
  symbol outside clojure.core, a book name shadowing core, or a local
  (uniquify has renamed locals, so they never match) is not core."
  [f]
  (when (= :ref (:op f))
    (let [s (:name f)]
      (when (and (or (nil? (namespace s)) (= "clojure.core" (namespace s)))
                 (not (and (nil? (namespace s)) (contains? *opaque* s))))
        (symbol (name s))))))

(defn- numeric? [t]
  (or (and (lit? t) (number? (lv t)))
      (and (= :ref (:op t)) (contains? *numeric* (:name t)))
      (and (= :invoke (:op t)) (contains? arithmetic (core-name (:fn t))))
      (and (= :invoke (:op t)) (= :ref (:op (:fn t)))
           (nil? (namespace (:name (:fn t))))
           (contains? *numeric-fns* (:name (:fn t))))))

(defn- zero-lit? [t] (and (lit? t) (= 0 (lv t))))
(defn- one-lit? [t] (and (lit? t) (= 1 (lv t))))

(defn- reduce-invoke [f args]
  (let [nm (core-name f)
        stuck {:op :invoke :fn f :args args}]
    (cond
      (nil? nm) stuck
      (and (= '+ nm) (= 2 (count args)) (zero-lit? (first args)) (numeric? (second args)))
      (second args)
      (and (= '+ nm) (= 2 (count args)) (zero-lit? (second args)) (numeric? (first args)))
      (first args)
      (and (= '* nm) (= 2 (count args)) (one-lit? (first args)) (numeric? (second args)))
      (second args)
      (and (= '* nm) (= 2 (count args)) (one-lit? (second args)) (numeric? (first args)))
      (first args)
      (and (every? lit? args) (get builtins nm))
      (try {:op :lit :val (apply (get builtins nm) (map lv args))}
           (catch Throwable _ {:op :error :form stuck}))
      :else stuck)))

(defn- const-match?
  "Case test constants are unevaluated: a list test is a GROUP whose members
  each match (Clojure: (case x (1 2) :small :big)), so the quoted constant
  `'a` matches the scrutinee `a` or `quote` -- exactly what jolt/Clojure do."
  [v test]
  (if (seq? test)
    (boolean (some (fn [m] (= v m)) test))
    (= v test)))

(declare norm)

(defn- norm-let [bs body op]
  (if (empty? bs)
    (norm body)
    (let [[b v] (first bs)
          v* (norm v)
          rest-t (if (next bs) {:op op :bindings (vec (rest bs)) :body body} body)]
      (cond
        ;; strict: only a value may be substituted (a throwing init must
        ;; not be dropped or moved under a branch)
        (and (= :let op) (symbol? b) (value? v*)) (norm (subst rest-t b v*))
        ;; (let [y e] y) is e
        (and (= :let op) (nil? (next bs)) (= :ref (:op body)) (= b (:name body))) v*
        :else {:op op :bindings (into [[b v*]] (map (fn [[b v]] [b (norm v)]) (rest bs)))
               :body (norm body)}))))

(defn norm
  "Reduce a uniquified AST toward a normal form."
  [ast]
  (case (:op ast)
    :lit ast
    :ref ast
    :error ast
    :if (let [c (norm (:test ast))]
          (if (lit? c)
            (norm (if (truthy? (lv c)) (:then ast) (:else ast)))
            (assoc ast :test c :then (norm (:then ast)) :else (norm (:else ast)))))
    ;; a statement that is a value has no effect; any other is kept
    :do (let [ss (remove value? (map norm (:stmts ast)))
              r (norm (:ret ast))]
          (if (empty? ss) r {:op :do :stmts (vec ss) :ret r}))
    :let (norm-let (:bindings ast) (:body ast) :let)
    :loop (assoc ast :bindings (mapv (fn [[b v]] [b (norm v)]) (:bindings ast))
                     :body (norm (:body ast)))
    :invoke (let [f (norm (:fn ast))
                  args (mapv norm (:args ast))
                  ps (:params f)]
              ;; ((fn [x] body) v): beta when every argument is a value
              (if (and (= :fn (:op f)) (nil? (:name f))
                       (= (count ps) (count args))
                       (= (:writ/arity f) {:min (count ps) :max (count ps)})
                       (every? value? args))
                (norm (reduce (fn [b [p a]] (subst b p a)) (:body f) (map vector ps args)))
                (reduce-invoke f args)))
    :fn (assoc ast :body (norm (:body ast)))
    :recur (assoc ast :args (mapv norm (:args ast)))
    :case (let [s (norm (:scrut ast))]
            (if (lit? s)
              (if-let [hit (some (fn [c] (when (const-match? (lv s) (:test c)) c))
                                 (:clauses ast))]
                (norm (:body hit))
                (if (:default ast)
                  (norm (:default ast))
                  {:op :error :form ast}))
              (assoc ast :scrut s
                         :clauses (mapv (fn [c] (assoc c :body (norm (:body c)))) (:clauses ast))
                         :default (when (:default ast) (norm (:default ast))))))
    :vec (assoc ast :items (mapv norm (:items ast)))
    :set (assoc ast :items (mapv norm (:items ast)))
    :map (assoc ast :keys (mapv norm (:keys ast))
                    :vals (mapv norm (:vals ast)))
    ast))

;; --- alpha ---------------------------------------------------------------

(defn- canon
  "Rename every binder to its position in walk order, so alpha-equivalent
  terms compare equal."
  [ast]
  (let [n (atom 0)
        fresh (fn [] (symbol (str "%" (swap! n inc))))]
    (letfn [(c [t env]
              (case (:op t)
                :ref (assoc t :name (get env (:name t) (:name t)))
                :fn (let [nm* (when (:name t) (fresh))
                          ps* (mapv (fn [p] (when p (fresh))) (:params t))
                          env* (cond-> (into env (map vector (remove nil? (:params t))
                                                      (remove nil? ps*)))
                                 (:name t) (assoc (:name t) nm*))]
                      {:op :fn :name nm* :params ps* :body (c (:body t) env*)})
                (:let :loop) (let [[bs env*] (reduce (fn [[acc e] [b v]]
                                                       (let [b* (fresh)]
                                                         [(conj acc [b* (c v e)]) (assoc e b b*)]))
                                                     [[] env] (:bindings t))]
                               {:op (:op t) :bindings bs :body (c (:body t) env*)})
                :if {:op :if :test (c (:test t) env) :then (c (:then t) env) :else (c (:else t) env)}
                :do {:op :do :stmts (mapv #(c % env) (:stmts t)) :ret (c (:ret t) env)}
                :invoke {:op :invoke :fn (c (:fn t) env) :args (mapv #(c % env) (:args t))}
                :recur {:op :recur :args (mapv #(c % env) (:args t))}
                :case {:op :case :scrut (c (:scrut t) env)
                       :clauses (mapv (fn [cl] {:test (:test cl) :body (c (:body cl) env)})
                                      (:clauses t))
                       :default (when (:default t) (c (:default t) env))}
                (:vec :set) {:op (:op t) :items (mapv #(c % env) (:items t))}
                :map {:op :map :keys (mapv #(c % env) (:keys t)) :vals (mapv #(c % env) (:vals t))}
                :lit {:op :lit :val (:val t)}
                :error {:op :error}
                t))]
      (c ast {}))))

(defn norm-form
  "Normalise a Clojure form: lower, uniquify, reduce, canonicalise binders."
  [form]
  (canon (norm (l/uniquify (l/lower form)))))

(defn- has-op? [t op]
  (boolean (some #(and (map? %) (= op (:op %))) (tree-seq coll? seq t))))

(defn throws?
  "Does the normal form contain a term that is known to throw?"
  [nf]
  (has-op? nf :error))

(defn has-fn?
  "Does the normal form contain an fn value?"
  [nf]
  (has-op? nf :fn))

(defn convertible?
  "Do two Clojure forms have the same normal form, up to alpha?"
  [a b]
  (= (norm-form a) (norm-form b)))
