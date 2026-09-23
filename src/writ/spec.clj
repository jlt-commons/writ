(ns writ.spec
  "A spec namespace: the contract for another namespace, kept entirely
  outside it.

    (ns my.app.spec
      (:require [writ.spec :refer [spec data ann law]]))

    (spec my.app)                                ; the namespace it constrains
    (ann isort [(List Nat) -> (List Nat)])       ; a public fn's signature
    (law sorted (forall [xs (List Nat)] (ascending? (isort xs))))

  The implementation is plain Clojure and never mentions writ.  `check`
  reads its source and runs writ's static rules over it with the types the
  spec gives, then discharges each law:

  * proved     -- writ.norm shows it for every input (no code is run)
  * evaluated  -- a closed law, decided by running the code once
  * tested     -- a universal law, run by test.check against inputs generated
                  from the binders' types; a failure is shrunk to the
                  smallest input that still breaks it, and its seed replays it
  * witnessed  -- an existential, with the generated value that satisfies it

  Tested is not proved: the report says which one each law got.
  `instrument` wraps the target's fns with the signatures' runtime checks."
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [writ.book :as book]
            [writ.check :as ck]
            [writ.data :as dt]
            [writ.kind :as kind]
            [writ.law :as lw]
            [writ.norm :as norm]
            [writ.types :as ty]
            [clojure.test.check :as tc]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]))

(defn- fail! [& msg]
  (throw (ex-info (str "Writ: " (apply str msg)) {:writ/error true})))

;; --- the spec surface ----------------------------------------------------

(def registry
  "spec ns name -> {:target sym :data [form] :anns {name sig} :laws [law]}"
  (atom {}))

(defn- simple-sym? [x] (and (symbol? x) (nil? (namespace x))))

(defn parse-ann
  "`[A B -> R]` into {:params [A B] :ret R}."
  [nm sig]
  (when-not (simple-sym? nm)
    (fail! "`ann` needs a simple fn name, had: `" (pr-str nm) "`"))
  (when-not (vector? sig)
    (fail! "`ann " nm "` needs a signature vector like [A B -> R]"))
  (let [[ps [arrow & rs]] (split-with #(not= '-> %) sig)]
    (when-not (and (= '-> arrow) (= 1 (count rs)))
      (fail! "`ann " nm "` must end in `-> ReturnType`, had: " (pr-str sig)))
    {:params (vec ps) :ret (first rs)}))

(defn -register! [spec-ns k v]
  (swap! registry update spec-ns
         (fn [e] (case k
                   :target {:target v :data [] :anns {} :laws []}
                   :data (update e :data conj v)
                   :ann (assoc-in e [:anns (first v)] (second v))
                   :law (update e :laws conj v))))
  nil)

(defmacro spec
  "Name the namespace this spec constrains.  Comes first."
  [target]
  (when-not (simple-sym? target)
    (fail! "`spec` names a namespace symbol, had: `" (pr-str target) "`"))
  `(-register! '~(ns-name *ns*) :target '~target))

(defmacro data
  "Declare a datatype the target's values use, as writ.defn/data."
  [& args]
  (let [f (cons 'data args)]
    (dt/parse f)
    `(-register! '~(ns-name *ns*) :data '~f)))

(defmacro ann
  "Give a target fn its signature: (ann f [A B -> R])."
  [nm sig]
  `(-register! '~(ns-name *ns*) :ann '~[nm (parse-ann nm sig)]))

(defmacro law
  "State a law about the target's behaviour."
  [nm prop]
  (when-not (simple-sym? nm)
    (fail! "a `law` name must be a simple symbol: `" (pr-str nm) "`"))
  `(-register! '~(ns-name *ns*) :law '~{:name nm :prop prop}))

;; --- propositions ----------------------------------------------------------

(defn- head? [f s]
  (and (seq? f) (symbol? (first f)) (= s (name (first f)))))

(defn- quant? [p] (or (head? p "forall") (head? p "exists")))

(defn desugar
  "Multi-binder quantifiers, (forall [x A, y B] P), into nested ones, the
  single-binder shape writ.law reads."
  [p]
  (cond
    (quant? p)
    (let [[q bs body & more] p]
      (when-not (and (vector? bs) (seq bs) (even? (count bs))
                     (every? simple-sym? (take-nth 2 bs)) (some? body) (empty? more))
        (fail! "`" (name q) "` must be (" (name q) " [x T ...] P), had: " (pr-str p)))
      (reduce (fn [acc [x t]] (list (symbol (name q)) [x t] acc))
              (desugar body)
              (reverse (partition 2 bs))))
    (or (head? p "and") (head? p "=>"))
    (cons (first p) (map desugar (rest p)))
    :else p))

(defn- auto-proof
  "The proof term a law's shape dictates, for writ.law/prove: refl for an
  equality, pair for a conjunction, fn for a universal or implication (a
  conclusion equal to its hypothesis cites it).  nil when the shape has no
  static proof (a predicate, an existential)."
  [p]
  (cond
    (head? p "=") 'refl
    (head? p "and") (let [ts (map auto-proof (rest p))]
                      (when (every? some? ts) (cons 'pair ts)))
    (head? p "=>") (let [h (gensym "h")]
                     (if (= (nth p 1) (nth p 2))
                       (list 'fn [h] h)
                       (when-let [t (auto-proof (nth p 2))] (list 'fn [h] t))))
    (head? p "forall") (let [[_ [x _] body] p]
                         (when-let [t (auto-proof body)] (list 'fn [x] t)))
    :else nil))

(defn- try-prove
  "true when writ.norm discharges `p` statically."
  [p tenv opaque numeric-fns]
  (when-let [t (auto-proof p)]
    (try
      (binding [norm/*opaque* opaque
                norm/*numeric-fns* numeric-fns]
        (lw/prove p t {:laws {} :hyps {} :numeric #{} :tenv tenv}))
      true
      (catch Throwable _ false))))

;; --- types at runtime --------------------------------------------------------

(defn- plain [t]
  (cond (symbol? t) (symbol (name t))
        (seq? t) (apply list (map plain t))
        :else t))

(defn- subst [t m]
  (cond (symbol? t) (get m t t)
        (seq? t) (apply list (map #(subst % m) t))
        :else t))

(defn- ctor-info
  "[ctor-sym {:fields [types]}] for a data value's constructor, with the
  type's parameters instantiated at `args`."
  [decl args c]
  (when-let [info (get (:ctors decl) c)]
    (let [m (zipmap (:params decl) args)]
      {:fields (mapv #(subst % m) (:fields info))})))

(defn- data-decl [t tenv]
  (let [h (if (seq? t) (first t) t)]
    (when-let [d (get tenv h)]
      (when-not (:tvar d) [d (if (seq? t) (vec (rest t)) [])]))))

(declare conforms?)

(defn- conforms-data?
  "A data value is a vector headed by its constructor keyword, one element
  per field: [:Leaf], [:Node l v r]."
  [d args v tenv]
  (let [info (when (and (vector? v) (keyword? (first v)))
               (ctor-info d args (symbol (name (first v)))))]
    (boolean
      (and info
           (= (count (:fields info)) (dec (count v)))
           (every? true? (map #(conforms? %1 %2 tenv) (:fields info) (rest v)))))))

(defn conforms?
  "Does value `v` fit type `t`?  Unknown types and type variables pass."
  [t v tenv]
  (let [t (plain t)]
    (cond
      (symbol? t)
      (case t
        Nat (nat-int? v)
        Int (int? v)
        Bool (boolean? v)
        String (string? v)
        Char (char? v)
        Keyword (keyword? v)
        Symbol (symbol? v)
        (Float Double) (number? v)
        Unit (nil? v)
        Any true
        (if-let [[d args] (data-decl t tenv)]
          (conforms-data? d args v tenv)
          true))

      (seq? t)
      (let [[h & as] t]
        (case h
          List (and (or (nil? v) (sequential? v)) (every? #(conforms? (first as) % tenv) v))
          Vec (and (vector? v) (every? #(conforms? (first as) % tenv) v))
          Set (and (set? v) (every? #(conforms? (first as) % tenv) v))
          Map (and (map? v) (every? (fn [[k x]] (and (conforms? (first as) k tenv)
                                                     (conforms? (second as) x tenv))) v))
          (Tuple &) (and (vector? v) (= (count as) (count v))
                         (every? true? (map #(conforms? %1 %2 tenv) as v)))
          -> (ifn? v)
          (if-let [[d args] (data-decl t tenv)]
            (conforms-data? d args v tenv)
            true)))

      :else true)))

;; --- generators ---------------------------------------------------------------
;; Values come from test.check generators built from the spec's types, so a
;; failure shrinks through test.check's rose trees and a seed replays it.

(defn- mentions? [t nm]
  (boolean (some #{nm} (tree-seq seq? seq (if (seq? t) t (list t))))))

(declare type->gen)

(defn- data-gen
  "A data value is a vector headed by its constructor keyword: [:Leaf],
  [:Node l v r].  Recursive fields get half the size, and at size 0 only
  the constructors that do not recurse are picked, so values stay finite."
  [d args nm tenv]
  (let [ctors (sort-by str (keys (:ctors d)))
        fields (fn [c] (:fields (ctor-info d args c)))
        base (remove (fn [c] (some #(mentions? % nm) (fields c))) ctors)
        ctor-gen (fn [c size]
                   (let [k (keyword (name c))
                         fs (fields c)]
                     (if (empty? fs)
                       (gen/return [k])
                       (gen/fmap #(into [k] %)
                                 (apply gen/tuple
                                        (map #(gen/resize (quot size 2) (type->gen % tenv)) fs))))))]
    (gen/sized (fn [size]
                 (let [pick (if (and (<= size 1) (seq base)) base ctors)]
                   (gen/one-of (mapv #(ctor-gen % size) pick)))))))

(def ^:private finite-double
  (gen/double* {:NaN? false :infinite? false}))

(defn type->gen
  "The test.check generator for values of type `t`."
  [t tenv]
  (let [t (plain t)]
    (cond
      (symbol? t)
      (case t
        Nat gen/nat
        Int gen/small-integer
        Bool gen/boolean
        Char gen/char-alpha
        String gen/string-alphanumeric
        Keyword gen/keyword
        Symbol gen/symbol
        (Float Double) finite-double
        Unit (gen/return nil)
        Any (gen/one-of [gen/small-integer gen/string-alphanumeric gen/keyword
                         (gen/vector gen/small-integer)])
        (if-let [[d args] (data-decl t tenv)]
          (data-gen d args t tenv)
          (fail! "cannot generate values of type `" t "`: declare it with `data`")))

      (seq? t)
      (let [[h & as] t
            el #(type->gen (nth as %) tenv)]
        (case h
          ;; a (List T) is any seq Clojure hands around: a list, a vector,
          ;; a lazy seq or nil.  Shrinking prefers the list.
          List (let [g (el 0)]
                 (gen/frequency [[3 (gen/list g)]
                                 [3 (gen/vector g)]
                                 [2 (gen/fmap #(map identity %) (gen/list g))]
                                 [1 (gen/return nil)]]))
          Vec (gen/vector (el 0))
          Set (gen/set (el 0))
          Map (gen/map (el 0) (el 1))
          (Tuple &) (apply gen/tuple (map #(type->gen % tenv) as))
          -> (fail! "cannot generate functions: quantify over data, not `" (pr-str t) "`")
          (if-let [[d args] (data-decl t tenv)]
            (data-gen d args h tenv)
            (fail! "cannot generate values of type `" (pr-str t) "`"))))

      :else (fail! "cannot generate values of type `" (pr-str t) "`"))))

(defn sample
  "`n` generated values of type `t`, for a look at what laws are run on."
  ([t tenv] (sample t tenv 10))
  ([t tenv n] (gen/sample (type->gen t tenv) n)))

;; --- evaluating laws ---------------------------------------------------------

(defn- qualify
  "Resolve a law's free names the way the spec reads them: a target public
  first, then a name the spec ns interns; bound names and anything else
  (core, aliases) are left for eval in the spec ns."
  [form bound target-publics spec-interns target spec-ns]
  (letfn [(walk [f bound]
            (cond
              (and (symbol? f) (nil? (namespace f)) (not (contains? bound f)))
              (cond (contains? target-publics f) (symbol (name target) (name f))
                    (contains? spec-interns f) (symbol (name spec-ns) (name f))
                    :else f)
              (and (seq? f) (= 'quote (first f))) f
              (and (seq? f) (quant? f))
              (let [[q [x t] body] f] (list q [x t] (walk body (conj bound x))))
              (seq? f) (apply list (map #(walk % bound) f))
              (vector? f) (mapv #(walk % bound) f)
              (map? f) (into {} (map (fn [[k v]] [(walk k bound) (walk v bound)])) f)
              (set? f) (into #{} (map #(walk % bound)) f)
              :else f))]
    (walk form bound)))

(defn- evaluator
  "Compile and cache term fns: (ev vars term env) runs `term` with the
  variables bound from env."
  [spec-ns]
  (let [cache (atom {})]
    (fn [vars term env]
      (let [k [vars term]
            f (or (get @cache k)
                  (let [f (binding [*ns* (the-ns spec-ns)]
                            (eval (list 'fn (vec vars) term)))]
                    (swap! cache assoc k f)
                    f))]
        (apply f (map #(get env %) vars))))))

(defn- run-term
  "{:ok v} or {:thrown msg}."
  [ctx term env]
  (try {:ok ((:ev ctx) (:vars ctx) term env)}
       (catch Throwable e {:thrown (or (ex-message e) (str e))})))

(defn- literal? [x]
  (or (number? x) (string? x) (keyword? x) (char? x) (boolean? x) (nil? x)
      (and (coll? x) (empty? x))))

(declare holds)

(defn- sample-quant
  "A nested quantifier: sampled over a handful of generated values."
  [ctx [q [x t] body] env]
  (let [ctx* (update ctx :vars conj x)
        vals (gen/sample (type->gen t (:tenv ctx)) 20)
        rs (map #(holds ctx* body (assoc env x %)) vals)]
    (if (= "forall" (name q))
      (or (first (filter #(= :fail (:result %)) rs)) {:result :pass})
      (or (first (filter #(= :pass (:result %)) rs))
          {:result :fail :detail [[(list q [x t] '...) "no witness among 20 samples"]]}))))

(defn holds
  "Evaluate proposition `p` under env: {:result :pass|:fail|:discard
  :detail [[term value-or-note]]}."
  [ctx p env]
  (cond
    (head? p "=")
    (let [[_ a b] p
          ra (run-term ctx a env)
          rb (run-term ctx b env)
          show (fn [r] (if (contains? r :ok) (pr-str (:ok r)) (str "threw: " (:thrown r))))]
      (if (and (contains? ra :ok) (contains? rb :ok) (= (:ok ra) (:ok rb)))
        {:result :pass}
        {:result :fail :detail [[a (show ra)] [b (show rb)]]}))

    (head? p "and")
    (or (first (remove #(= :pass (:result %)) (map #(holds ctx % env) (rest p))))
        {:result :pass})

    (head? p "=>")
    (let [h (holds ctx (nth p 1) env)]
      (if (= :pass (:result h))
        (holds ctx (nth p 2) env)
        {:result :discard}))

    (quant? p) (sample-quant ctx p env)

    :else
    (let [r (run-term ctx p env)]
      (cond
        (:thrown r) {:result :fail :detail [[p (str "threw: " (:thrown r))]]}
        (:ok r) {:result :pass}
        :else
        {:result :fail
         :detail (into [[p (pr-str (:ok r))]]
                       (when (seq? p)
                         (keep (fn [a]
                                 (when-not (or (literal? a) (symbol? a))
                                   (let [ra (run-term ctx a env)]
                                     [a (if (contains? ra :ok) (pr-str (:ok ra))
                                            (str "threw: " (:thrown ra)))])))
                               (rest p))))}))))

(defn- leading-foralls [p]
  (loop [p p, bs []]
    (if (head? p "forall")
      (let [[_ [x t] body] p] (recur body (conj bs [x t])))
      [bs p])))

(defn- test-law
  [ctx {:keys [name prop]} {:keys [trials seed max-size]}]
  (let [[bs body] (leading-foralls prop)
        qc (fn [p] (tc/quick-check trials p :seed seed :max-size max-size))]
    (cond
      ;; closed: run it once
      (and (empty? bs) (not (quant? body)))
      (let [r (holds (assoc ctx :vars []) body {})]
        (if (= :pass (:result r))
          {:law name :status :evaluated}
          {:law name :status :failed :counterexample {}
           :detail (or (:detail r) [[body "the hypothesis does not hold"]])}))

      ;; existential: a witness is a counterexample to its negation, so
      ;; test.check finds it and shrinks it to the simplest one
      (and (empty? bs) (head? body "exists"))
      (let [[_ [x t] inner] body
            ctx* (assoc ctx :vars [x])
            res (qc (prop/for-all* [(type->gen t (:tenv ctx))]
                                   (fn [v] (not= :pass (:result (holds ctx* inner {x v}))))))]
        (if (:pass? res)
          {:law name :status :failed :counterexample {} :seed (:seed res)
           :detail [[body (str "no witness among " (:num-tests res) " generated values")]]}
          {:law name :status :witnessed :seed (:seed res)
           :witness {x (first (get-in res [:shrunk :smallest]))}}))

      :else
      (let [vars (mapv first bs)
            ctx* (assoc ctx :vars vars)
            discards (atom 0)
            res (qc (prop/for-all* (mapv #(type->gen (second %) (:tenv ctx)) bs)
                                   (fn [& vals]
                                     (case (:result (holds ctx* body (zipmap vars vals)))
                                       :pass true
                                       :discard (do (swap! discards inc) true)
                                       false))))]
        (cond
          (not (:pass? res))
          (let [small (zipmap vars (get-in res [:shrunk :smallest]))]
            {:law name :status :failed
             :counterexample small
             :original (zipmap vars (:fail res))
             :trial (:num-tests res) :seed (:seed res)
             :detail (:detail (holds ctx* body small))})

          (= @discards (:num-tests res))
          {:law name :status :failed :counterexample {} :seed (:seed res)
           :detail [[body (str "the hypothesis never held in " (:num-tests res) " trials")]]}

          :else
          {:law name :status :tested :trials (:num-tests res) :seed (:seed res)
           :discarded @discards})))))

;; --- the target's source -----------------------------------------------------

(defn- source-url [target]
  (let [base (-> (name target) (str/replace "-" "_") (str/replace "." "/"))]
    (or (io/resource (str base ".clj")) (io/resource (str base ".cljc"))
        (fail! "cannot find the source of `" target "` on the classpath"))))

(defn- defn-parts
  "[name docstring? attrs? params body] positions for a defn form."
  [f]
  (let [[h nm & tail] f
        doc (when (string? (first tail)) (first tail))
        tail (if doc (rest tail) tail)
        attrs (when (map? (first tail)) (first tail))
        tail (if attrs (rest tail) tail)]
    {:head h :name nm :doc doc :attrs attrs :params (first tail) :body (rest tail)}))

(defn- annotate-defn
  "Put a spec signature on a plain defn: param types as :writ/type, the
  return type as the name's :tag -- where writ's checker reads them."
  [f sig]
  (let [{:keys [head name doc attrs params body]} (defn-parts f)]
    (when-not (vector? params)
      (fail! "`" name "` is multi-arity; `ann` gives a single signature"))
    (let [fixed (vec (take-while #(not= '& %) params))
          rest? (some #{'&} params)]
      (when (if rest?
              (< (count (:params sig)) (count fixed))
              (not= (count (:params sig)) (count fixed)))
        (fail! "`ann " name "` gives " (count (:params sig)) " parameter type(s) but `"
               name "` takes " (count fixed)))
      (let [types (:params sig)
            params* (loop [ps params, ts types, out []]
                      (cond
                        (empty? ps) out
                        (= '& (first ps)) (into out ps)
                        (symbol? (first ps))
                        (recur (rest ps) (rest ts)
                               (conj out (vary-meta (first ps) assoc :writ/type (first ts))))
                        :else (recur (rest ps) (rest ts) (conj out (first ps)))))]
        (apply list (concat [head (vary-meta name assoc :tag (:ret sig))]
                            (when doc [doc]) (when attrs [attrs])
                            [params*] body))))))

(defn- static-check
  "Run writ's rules over the target's source with the spec's types.
  Returns {:ok true :defns {name private?}} or {:ok false :error msg}."
  [{:keys [target data anns]}]
  (try
    (let [forms (book/read-forms (source-url target))
          defns (into {} (keep (fn [f] (when (ck/defn-form? f)
                                         (let [p (defn-parts f)]
                                           [(:name p) (or (= "defn-" (name (first f)))
                                                          (boolean (:private (meta (:name p)))))]))))
                      forms)
          missing (remove #(contains? defns %) (sort (keys anns)))]
      (when (seq missing)
        (fail! "the spec gives `" (first missing) "` a signature, but `" target
               "` defines no fn `" (first missing) "`"))
      (let [forms* (mapv (fn [f]
                           (if (and (ck/defn-form? f) (contains? anns (second f)))
                             (annotate-defn f (get anns (second f)))
                             f))
                         forms)
            [nsf others] [(filter #(head? % "ns") forms*) (remove #(head? % "ns") forms*)]]
        (binding [ck/*affine* false
                  ck/*descend-all* true
                  ty/*tagged* true]
          (book/check-book (vec (concat nsf data others))))
        {:ok true :defns defns}))
    (catch Throwable e
      {:ok false :error (or (ex-message e) (str e))})))

(defn- tenv-of [data]
  (into {} (map (fn [f] (let [d (dt/parse f)] [(:name d) (dt/env d)]))) data))

;; --- instrument --------------------------------------------------------------

(def ^:private originals (atom {}))

(defn- arg-names [v n]
  (let [al (first (filter #(= n (count (take-while (fn [p] (not= '& p)) %)))
                          (:arglists (meta v))))]
    (vec (or al (map #(symbol (str "arg" %)) (range n))))))

(defn- checked [nm f sig tenv argn]
  (fn [& args]
    (doseq [[i t a] (map vector (range) (:params sig) args)]
      (when-not (conforms? t a tenv)
        (fail! "`" nm "` argument " (inc i) " (" (nth argn i (str "arg" i)) ") expects "
               (pr-str t) ", got " (pr-str a))))
    (let [r (apply f args)]
      (when-not (conforms? (:ret sig) r tenv)
        (fail! "`" nm "` returns " (pr-str (:ret sig)) ", but returned " (pr-str r)
               " for arguments " (pr-str (vec args))))
      r)))

(defn- entry [spec-ns target]
  (require spec-ns)
  (let [e (get @registry spec-ns)]
    (when-not e
      (fail! "`" spec-ns "` is not a spec namespace: it has no `(spec target-ns)` form"))
    (let [e (if target (assoc e :target target) e)]
      (require (:target e))
      e)))

(defn- wrap!
  "Wrap the signed fns not already wrapped; returns the vars it wrapped."
  [{:keys [target anns data]}]
  (let [tenv (tenv-of data)]
    (vec (for [[nm sig] anns
               :let [v (ns-resolve (the-ns target) nm)]
               :when (and v (not (contains? @originals v)))]
           (let [f @v]
             (swap! originals assoc v f)
             (alter-var-root v (constantly (checked nm f sig tenv (arg-names v (count (:params sig))))))
             v)))))

(defn- unwrap! [vars]
  (doseq [v vars :when (contains? @originals v)]
    (alter-var-root v (constantly (get @originals v)))
    (swap! originals dissoc v)))

(defn instrument
  "Wrap every fn the spec signs with its runtime argument and return
  checks.  Undo with `unstrument`."
  ([spec-ns] (instrument spec-ns nil))
  ([spec-ns target]
   (let [e (entry spec-ns target)]
     (wrap! e)
     (:target e))))

(defn unstrument
  "Restore the fns `instrument` wrapped."
  ([spec-ns] (unstrument spec-ns nil))
  ([spec-ns target]
   (let [{:keys [target anns]} (entry spec-ns target)]
     (unwrap! (keep #(ns-resolve (the-ns target) %) (keys anns)))
     target)))

;; --- check ---------------------------------------------------------------------

(defn- format-failure [{:keys [law counterexample detail original trial seed error]}]
  (let [pad (apply max 0 (map (comp count str) (keys counterexample)))]
    (str "law `" law "` fails"
         (if (seq counterexample)
           (str " for\n"
                (str/join "\n" (map (fn [[k v]] (str "  " k (apply str (repeat (- pad (count (str k))) " "))
                                                     " = " (pr-str v)))
                                    (sort-by (comp str key) counterexample))))
           "")
         "\n"
         (str/join "\n" (map (fn [[t v]] (str "  " (pr-str t) " => " v)) detail))
         (when error (str "  " error))
         (when (and original (not= original counterexample))
           (str "\n  (shrunk from " (pr-str original) ", failing on test " trial ")"))
         (when seed (str "\n  (replay with {:seed " seed "})")))))

(defn format-report
  "The report as text for an agent or a person: what failed and why."
  [{:keys [ok target spec static laws unspecified]}]
  (str "writ.spec: " spec " against " target (if ok ": ok" ": FAILED")
       (when-not (:ok static) (str "\n\n" (:error static)))
       (apply str (map #(str "\n\n" (format-failure %)) (filter #(= :failed (:status %)) laws)))
       (when (seq unspecified)
         (str "\n\nnot in the spec (no signature): " (str/join ", " unspecified)))))

(defn check
  "Check a spec namespace against its target (or opts :target).  Returns a
  report map; :ok says whether everything held and :message explains any
  failure.  opts: :target, :trials (test.check runs per law, default 100),
  :seed (default random; each law's report carries the one it used) and
  :max-size (the largest generated size, default 50)."
  ([spec-ns] (check spec-ns {}))
  ([spec-ns opts]
   (let [{:keys [trials seed max-size] :or {trials 100 max-size 50}} opts
         e (entry spec-ns (:target opts))
         {:keys [target anns data laws]} e
         static (static-check e)
         base {:spec spec-ns :target target
               :static (if (:ok static) {:ok true} static)
               :unspecified (vec (sort (for [[nm private?] (:defns static)
                                              :when (and (not private?) (not (contains? anns nm)))]
                                          nm)))}]
     (if-not (:ok static)
       (let [r (assoc base :ok false :laws [])]
         (assoc r :message (format-report r)))
       (let [tenv (tenv-of data)
             publics (set (keys (ns-publics (the-ns target))))
             interns (set (keys (ns-interns (the-ns spec-ns))))
             opaque (into (set publics) interns)
             numeric-fns (into #{} (keep (fn [[k s]] (when (contains? '#{Nat Int Float Double}
                                                                      (plain (:ret s)))
                                                       k)))
                               anns)
             ctx {:ev (evaluator spec-ns) :tenv tenv}
             ;; only what this check wrapped is unwrapped after it, so a
             ;; caller's own instrument stays in place
             wrapped (wrap! e)
             results (try
                       (vec (for [{:keys [name prop]} laws
                                  :let [p (desugar prop)]]
                              (try
                                (lw/check-prop-shape! p)
                                (if (try-prove p tenv opaque numeric-fns)
                                  {:law name :status :proved}
                                  (test-law ctx {:name name
                                                 :prop (qualify p #{} publics interns target spec-ns)}
                                            {:trials trials :seed seed :max-size max-size}))
                                ;; a law that cannot be run (a malformed
                                ;; proposition, a type with no generator)
                                ;; fails with the reason, not the whole check
                                (catch Throwable ex
                                  {:law name :status :failed :counterexample {} :detail []
                                   :error (or (ex-message ex) (str ex))}))))
                       (finally (unwrap! wrapped)))
             unq (fn unq [f]
                   (cond (and (symbol? f) (contains? #{(name target) (name spec-ns)} (namespace f)))
                         (symbol (name f))
                         (seq? f) (apply list (map unq f))
                         (vector? f) (mapv unq f)
                         :else f))
             results (mapv (fn [r] (if (:detail r)
                                     (update r :detail (fn [d] (mapv (fn [[t v]] [(unq t) v]) d)))
                                     r))
                           results)
             r (assoc base :laws results
                           :ok (not-any? #(= :failed (:status %)) results))]
         (assoc r :message (format-report r)))))))

(defn check!
  "`check`, throwing with the report's message when anything fails."
  ([spec-ns] (check! spec-ns {}))
  ([spec-ns opts]
   (let [r (check spec-ns opts)]
     (if (:ok r)
       r
       (throw (ex-info (:message r) {:writ/error true :report r}))))))
