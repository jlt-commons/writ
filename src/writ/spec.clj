(ns writ.spec
  "A spec namespace: the contract for another namespace, kept entirely
  outside it.

    (ns my.app.spec
      (:require [writ.spec :refer [spec data ann law calls]]))

    (spec my.app)                                ; the namespace it constrains
    (ann isort [(List Nat) -> (List Nat)])       ; a public fn's signature
    (law sorted (forall [xs (List Nat)] (ascending? (isort xs))))

  A spec is the problem statement: the laws say what the code means, in
  the spec's own terms, not how it works.  The implementation is plain
  Clojure and never mentions writ.  `check` reads its source and runs
  writ's static rules over it with the types the spec gives, then checks
  the spec itself and each law:

  * vacuous    -- the law holds whatever the code does (writ.norm proves it
                  without the code, or it calls no target fn): it fails,
                  because it says nothing about the code
  * evaluated  -- a closed law, decided by running the code once
  * tested     -- a universal law, run by test.check against inputs generated
                  from the binders' types; a failure is shrunk to the
                  smallest input that still breaks it, and its seed replays it
  * witnessed  -- an existential, with the generated value that satisfies it

  Tested is not proved: the report says which one each law got.

  When every law holds, `check` asks whether the laws pin the code down:
  each signed public fn is swapped for well-typed impostors (a constant,
  an argument passed through, the real result perturbed, and one that
  differs off the literals every law fixes an argument to), and an
  impostor that still satisfies every law is a gap in the spec.  A passing
  report counts the impostors each fn's laws rejected.

  `(calls f [g ...])` states the exact set of fns `f` calls, read from its
  source; `call-graph` and `mermaid` show a namespace's graph.

  `instrument` wraps the target's fns with the signatures' runtime checks,
  and `scan` says which of a namespace's fns writ could check at all."
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [writ.book :as book]
            [writ.check :as ck]
            [writ.data :as dt]
            [writ.kind :as kind]
            [writ.law :as lw]
            [writ.lower :as l]
            [writ.norm :as norm]
            [writ.types :as ty]
            [writ.prove :as prover]
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
                   :target (merge {:target (first v) :data [] :anns {} :laws [] :calls [] :machines []}
                                  (second v))
                   :data (update e :data conj v)
                   :calls (update e :calls (fnil conj []) v)
                   :machine (update e :machines (fnil conj []) v)
                   :ann (assoc-in e [:anns (first v)] (second v))
                   :law (update e :laws conj v))))
  nil)

(def levels
  "What a law's evidence may be, strongest first.  A law is proved when the
  prover proves it, when it is closed and evaluates to true, or when an
  existential has a witness; tested when it only ran on generated inputs."
  [:proved :tested])

(defn- check-level! [where lv]
  (when-not (some #{lv} levels)
    (fail! where ": :require must be :proved or :tested, had: " (pr-str lv))))

(defmacro spec
  "Name the namespace this spec constrains.  Comes first.

    (spec my.sort)                     ; laws may be proved or only tested
    (spec my.sort {:require :proved})  ; every law must be proved

  Under {:require :proved} a law that is only tested fails the check,
  unless the law itself says why it cannot be proved yet."
  ([target] `(spec ~target {}))
  ([target opts]
   (when-not (simple-sym? target)
     (fail! "`spec` names a namespace symbol, had: `" (pr-str target) "`"))
   (when-not (map? opts)
     (fail! "`spec " target "` takes an options map after the namespace, had: " (pr-str opts)))
   (when-let [bad (seq (remove #{:require} (keys opts)))]
     (fail! "`spec " target "` has unknown options: " (pr-str bad) "; it takes :require"))
   (when (contains? opts :require) (check-level! (str "`spec " target "`") (:require opts)))
   `(-register! '~(ns-name *ns*) :target '~[target opts])))

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

(defn- resolve-callee
  "A callee as the spec writes it: a target fn by its simple name, or a fn
  of another namespace, whose alias in the spec namespace is resolved."
  [g]
  (if-let [n (namespace g)]
    (let [a (get (ns-aliases *ns*) (symbol n))]
      (symbol (if a (str (ns-name a)) n) (name g)))
    g))

(defmacro calls
  "State exactly which fns `f` calls: (calls f [g str/join]).  A simple
  name is a fn of the target; a qualified one is a fn of another
  namespace, through the spec's own aliases.  clojure.core and host
  members are not part of the call graph, and neither is `f` calling
  itself."
  [f gs]
  (when-not (simple-sym? f)
    (fail! "`calls` needs a simple fn name, had: `" (pr-str f) "`"))
  (when-not (and (vector? gs) (every? symbol? gs))
    (fail! "`calls " f "` needs a vector of fn names, had: " (pr-str gs)))
  `(-register! '~(ns-name *ns*) :calls '~[f (mapv resolve-callee gs)]))

(defmacro machine
  "State that a target fn steps a state machine by a transition table:

    (machine turnstile
      {:step step :start [:Locked]
       :transitions {[:Locked] {[:Coin] [:Unlocked]} ...}
       :final [[:Locked]] :never [[a b]] :before [[a b]]})

  `step` is run on every state and event (from its `ann` when those are
  data with field-less constructors, or :states and :events) and must give
  the table's state, or keep the state where the table lists nothing.  The
  table must reach every state from :start, and a :final state from every
  state it reaches; `:never [a b]` says no path leads from a to b, and
  `:before [a b]` that every path from :start to b passes through a."
  [nm m]
  (when-not (simple-sym? nm)
    (fail! "a `machine` name must be a simple symbol: `" (pr-str nm) "`"))
  (when-not (and (map? m) (simple-sym? (:step m)) (contains? m :start) (map? (:transitions m)))
    (fail! "`machine " nm "` needs a map with :step (a fn name), :start and :transitions"))
  (when-let [bad (seq (remove #{:step :start :transitions :final :never :before :states :events}
                              (keys m)))]
    (fail! "`machine " nm "` has unknown keys: " (pr-str bad)))
  `(-register! '~(ns-name *ns*) :machine '~[nm m]))

(defn- law-opts!
  "Check a law's options: :require sets the evidence it needs, and
  :require :tested needs :because, the reason it cannot be proved yet."
  [nm opts]
  (let [where (str "`law " nm "`")]
    (when-let [bad (seq (remove #{:require :because} (keys opts)))]
      (fail! where " has unknown options: " (pr-str bad) "; it takes :require and :because"))
    (when (contains? opts :require) (check-level! where (:require opts)))
    (when (and (= :tested (:require opts)) (not (and (string? (:because opts))
                                                     (not (str/blank? (:because opts))))))
      (fail! where " is let off proof with {:require :tested}, so it needs :because, a "
             "string saying why it cannot be proved yet"))
    (when (and (contains? opts :because) (not= :tested (:require opts)))
      (fail! where ": :because goes with :require :tested, the reason a law is only tested"))
    opts))

(defmacro law
  "State a law about the target's behaviour.

    (law sorted (forall [xs (List Nat)] (ascending? (isort xs))))
    (law sorted {:require :proved} (forall ...))   ; this law must be proved
    (law fast {:require :tested :because \"...\"} (forall ...))

  The options map is optional.  It overrides the spec's :require for this
  one law; letting a law off proof takes a reason, shown in every report."
  ([nm prop] `(law ~nm {} ~prop))
  ([nm opts prop]
   (when-not (simple-sym? nm)
     (fail! "a `law` name must be a simple symbol: `" (pr-str nm) "`"))
   (when-not (map? opts)
     (fail! "`law " nm "` takes (law name prop) or (law name {options} prop), had a "
            (pr-str opts) " where the options go"))
   (law-opts! nm opts)
   `(-register! '~(ns-name *ns*) :law '~(cond-> {:name nm :prop prop}
                                          (seq opts) (assoc :opts opts)))))

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

(defn- calls-target?
  "Does a qualified law mention any fn of the target namespace?"
  [qp target]
  (boolean (some #(and (symbol? %) (= (name target) (namespace %)))
                 (tree-seq coll? seq qp))))

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

(defn- binding-form?
  "A form whose arguments are not all expressions: a special form or a
  macro, such as `let`, whose binding vector cannot be evaluated alone.
  The connectives are kept, since each of their arguments is one."
  [p]
  (let [h (first p)]
    (and (symbol? h)
         (not (contains? '#{or and when if not} (symbol (name h))))
         (or (special-symbol? h)
             (boolean (some-> (ns-resolve (the-ns 'clojure.core) h) meta :macro))))))

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
                       (when (and (seq? p) (not (binding-form? p)))
                         (keep (fn [a]
                                 ;; a fn literal's value prints as an object
                                 (when-not (or (literal? a) (symbol? a)
                                               (and (seq? a) (contains? '#{fn fn*} (first a))))
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

;; --- adequacy: does the spec pin the code down? ------------------------------

(defn- other-value
  "A fn from a result to a different value of type `ret`, or nil when the
  type has only one value.  Types with no perturbation of their own take
  the first of a few generated values that differs from the result."
  [ret tenv seed]
  (let [h (if (seq? ret) (first ret) ret)]
    (case h
      (Nat Int) inc
      Bool not
      String #(str % "x")
      (Unit Any) nil
      (let [g (type->gen ret tenv)
            cands (distinct (map #(gen/generate g (* 3 %) (+ seed %)) (range 8)))]
        (when (next cands)
          (fn [r] (or (first (remove #(= r %) cands)) r)))))))

(defn- pinned-args
  "{i #{values}} for each argument position of `f` that every law calls it
  with a literal at: the laws say what `f` does there and nowhere else.
  Empty when some law uses `f` as a value rather than calling it, since
  then its arguments cannot be read off the law."
  [props f n]
  (let [forms (mapcat #(tree-seq coll? seq %) props)
        calls (filter #(and (seq? %) (= f (first %))) forms)
        lit? #(or (number? %) (string? %) (keyword? %) (char? %) (boolean? %) (nil? %))]
    (if (or (empty? calls) (not= (count calls) (count (filter #{f} forms))))
      {}
      (into {} (for [i (range n)
                     :let [as (map #(nth % (inc i) ::none) calls)]
                     :when (every? #(and (not= ::none %) (lit? %)) as)]
                 [i (set as)])))))

(defn impostors
  "Well-typed stand-ins for fn `nm` with signature `sig`: {:desc :kind
  :make}, where (make real-fn) is the impostor.  Constants of the return
  type, each argument of the return type passed through, the real result
  perturbed, and -- for each argument `pins` fixes to a set of literals --
  the real result on those literals and a different one everywhere else.
  A spec that means something rejects every one of them."
  [nm sig argn tenv seed & [pins]]
  (let [ret (plain (:ret sig))
        g (type->gen ret tenv)
        consts (distinct [(gen/generate g 0 seed) (gen/generate g 5 (inc seed))])
        other (other-value ret tenv seed)
        arg-name #(nth argn % (str "arg" %))
        wrap (fn [desc f] {:desc desc :kind :perturbed
                           :make (fn [real] (fn [& args] (f (apply real args))))})]
    (concat
      (for [v consts]
        {:desc (str "always returns " (pr-str v)) :kind :constant :make (fn [_] (fn [& _] v))})
      (keep-indexed (fn [i t]
                      (when (= (plain t) ret)
                        {:desc (str "returns its argument `" (arg-name i) "` unchanged")
                         :kind :pass-through
                         :make (fn [_] (fn [& args] (nth args i)))}))
                    (:params sig))
      (let [h (if (seq? ret) (first ret) ret)]
        (case h
          (Nat Int) [(wrap "returns one more than the real result" inc)]
          Bool [(wrap "returns the opposite of the real result" not)]
          String [(wrap "returns the real result with a character appended" #(str % "x"))]
          List [(wrap "returns the real result reversed" reverse)
                (wrap "returns the real result without its first element" rest)]
          Vec [(wrap "returns the real result reversed" #(vec (reverse %)))
               (wrap "returns the real result without its first element" #(vec (rest %)))]
          (when other [(wrap "returns a different value than the real result" other)])))
      (when other
        (for [[i vs] (sort-by key pins)
              :when (not (and (= 'Bool (plain (nth (:params sig) i nil)))
                              (= #{true false} vs)))
              :let [shown (str/join ", " (map pr-str (sort-by (fn [v] [(if (number? v) 0 1)
                                                                       (if (number? v) v 0)
                                                                       (pr-str v)])
                                                              vs)))
                    vs (vec vs)]]
          {:desc (str "returns a different value whenever `" (arg-name i)
                      "` is not one of " shown)
           :kind :off-pin
           :make (fn [real]
                   (fn [& args]
                     (let [r (apply real args)]
                       (if (some #(= % (nth args i)) vs) r (other r)))))})))))

(declare leading-foralls holds)

(defn- holds-sampled?
  "Does `prop` hold on `n` deterministic samples?  Existentials never
  reject an impostor; a law's own failure is what adequacy looks for."
  [ctx prop n seed]
  (let [[bs body] (leading-foralls prop)]
    (cond
      (and (empty? bs) (not (quant? body)))
      (not= :fail (:result (holds (assoc ctx :vars []) body {})))

      (empty? bs) true

      :else
      (let [vars (mapv first bs)
            ctx* (assoc ctx :vars vars)
            gens (mapv #(type->gen (second %) (:tenv ctx)) bs)]
        ;; each variable its own seed: with one seed, two variables of a
        ;; type get the same value every time, and a law relating them
        ;; never sees them differ
        (every? (fn [i]
                  (not= :fail (:result (holds ctx* body
                                              (zipmap vars (map-indexed
                                                             (fn [j g] (gen/generate g (mod i 30)
                                                                                     (+ seed i (* 7919 j))))
                                                             gens))))))
                (range n))))))

(defn- adequacy
  "Swap each signed public fn for its impostors, one at a time, and run
  every law against each.  Returns, per fn, [{:fn f :laws n :rejected
  [impostor] :survivors [desc]}]: a survivor is a gap in the spec."
  [ctx target fns anns props trials seed]
  (vec (for [nm fns
             :let [v (ns-resolve (the-ns target) nm)
                   real @v
                   sig (get anns nm)
                   argn (vec (take (count (:params sig)) (first (:arglists (meta v)))))
                   qnm (symbol (name target) (name nm))
                   pins (pinned-args props qnm (count (:params sig)))
                   survives? (fn [imp]
                               (try
                                 (alter-var-root v (constantly ((:make imp) real)))
                                 (every? #(holds-sampled? ctx % trials seed) props)
                                 (catch Throwable _ false)
                                 (finally (alter-var-root v (constantly real)))))
                   {survived true rejected false}
                   (group-by (comp boolean survives?)
                             (impostors nm sig argn (:tenv ctx) seed pins))]]
         {:fn nm
          :laws (count (filter #(some #{qnm} (tree-seq coll? seq %)) props))
          :rejected (mapv #(dissoc % :make) rejected)
          :survivors (mapv :desc survived)})))

;; --- the target's source -----------------------------------------------------

(def ^:private spec-forms-accepted
  (str "is not supported: in the code a spec covers, writ checks def and defn "
       "forms only (the ns form and comment blocks are skipped)"))

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
                        (or (symbol? (first ps)) (coll? (first ps)))
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
                  ty/*tagged* true
                  book/*forms-accepted* spec-forms-accepted]
          (book/check-book (vec (concat nsf data others))))
        {:ok true :defns defns}))
    (catch Throwable e
      {:ok false :error (or (ex-message e) (str e))})))

(defn- form-name [f]
  (when (and (seq? f) (symbol? (second f))) (second f)))

(defn scan
  "Which of `target`'s top-level forms writ could check, before any spec is
  written.  Reads the source from the classpath without loading it, and
  checks each form in order against the forms above it that passed.
  Returns {:target t :forms [{:name :head :private? :status :why}]}, with
  :status :ok, :needs-ann (it fails only because a collection it recurses
  over has no type, which an `ann` gives it) or :no, and :message, a
  summary to read."
  [target]
  (let [forms (book/read-forms (source-url target))
        nsf (filterv #(head? % "ns") forms)
        body (remove #(or (head? % "ns") (head? % "comment")) forms)
        rows (loop [fs body, kept [], blocked {}, out []]
               (if-let [f (first fs)]
                 (let [nm (form-name f)
                       dep (first (keep #(when (symbol? %)
                                           (let [s (symbol (name %))]
                                             (when (and (not= nm s) (contains? blocked s)) s)))
                                        (tree-seq coll? seq (rest f))))
                       [status why]
                       (if dep
                         [(get blocked dep)
                          (str "it uses `" dep "`, which "
                               (if (= :needs-ann (get blocked dep))
                                 "needs an `ann` first"
                                 "writ cannot check"))]
                         (try
                           (binding [ck/*affine* false
                                     ck/*descend-all* true
                                     ty/*tagged* true
                                     book/*forms-accepted* spec-forms-accepted]
                             (book/check-book (vec (concat nsf kept [f]))))
                           [:ok nil]
                           (catch Throwable e
                             (let [m (str/replace (or (ex-message e) (str e)) #"^Writ: " "")]
                               [(if (str/includes? m "must be a finite collection") :needs-ann :no)
                                m]))))]
                   (recur (rest fs)
                          (if (= :ok status) (conj kept f) kept)
                          (if (and nm (not= :ok status)) (assoc blocked nm status) blocked)
                          (conj out (cond-> {:name nm :head (first f) :status status
                                             :private? (boolean (or (head? f "defn-")
                                                                    (and nm (:private (meta nm)))))}
                                      why (assoc :why why)))))
                 out))
        label (fn [{:keys [name head private?]}]
                (str (or name head)
                     (when-not (contains? #{"defn" "defn-" "def"} (clojure.core/name head))
                       (str " (" head ")"))
                     (when private? " (private)")))
        group (fn [k title]
                (when-let [rs (seq (filter #(= k (:status %)) rows))]
                  (str "\n\n" title
                       (apply str (for [r rs]
                                    (str "\n  " (label r)
                                         (when (:why r) (str ": " (:why r)))))))))
        n (fn [k] (count (filter #(= k (:status %)) rows)))]
    {:target target
     :forms rows
     :message (str "writ.spec/scan " target ": " (n :ok) " of " (count rows)
                   " forms can be checked"
                   (when (pos? (n :needs-ann)) (str ", " (n :needs-ann) " more once signed"))
                   (group :ok "can be checked:")
                   (group :needs-ann "can be checked once an `ann` types its collection:")
                   (group :no "cannot be checked:"))}))

;; --- the call graph --------------------------------------------------------------

(defn- ns-names
  "The names an ns form brings in: {:aliases {alias lib} :refers {name
  lib/name}}, from its :require clauses."
  [ns-form]
  (reduce (fn [acc [lib & opts]]
            (let [o (apply hash-map (take (* 2 (quot (count opts) 2)) opts))]
              (cond-> acc
                (symbol? (:as o)) (assoc-in [:aliases (:as o)] lib)
                (sequential? (:refer o))
                (update :refers into (map (fn [r] [r (symbol (name lib) (name r))]))
                        (:refer o)))))
          {:aliases {} :refers {}}
          (for [clause (rest ns-form)
                :when (and (seq? clause) (= :require (first clause)))
                spec (rest clause)
                :when (or (vector? spec) (symbol? spec))]
            (if (symbol? spec) [spec] (seq spec)))))

(defn- callee
  "What a name in a body refers to in the call graph: the simple name of
  one of the namespace's own fns, or a qualified fn of another namespace.
  nil for clojure.core, host members, and anything else."
  [s own {:keys [aliases refers]}]
  (cond
    (nil? (namespace s)) (cond (contains? own s) s
                               (contains? refers s) (get refers s))
    (l/host-member? s) nil
    :else (let [q (symbol (namespace s))
                lib (get aliases q q)]
            (cond (contains? own (symbol (name s))) (when (= lib (:self aliases)) (symbol (name s)))
                  (= 'clojure.core lib) nil
                  :else (symbol (name lib) (name s))))))

(defn- body-refs
  "Every name a defn's body refers to, locals excluded.  The body is
  lowered and its binders renamed apart, so a local that shadows a fn is
  not a reference to it.  Code writ cannot lower is read as plain symbols."
  [params body own]
  (try
    (let [ast (binding [l/*locals* own]
                (l/uniquify (l/lower (list* 'fn params body))))]
      (keep #(when (and (map? %) (= :ref (:op %))) (:name %))
            (tree-seq coll? #(if (map? %) (vals %) (seq %)) ast)))
    (catch Throwable _
      (let [locals (set (mapcat l/binding-names params))]
        (remove locals (filter symbol? (tree-seq coll? seq body)))))))

(defn- graph-of
  "{f #{callee}} for each defn in `forms`, in the terms of `callee`."
  [forms]
  (let [nsf (first (filter #(head? % "ns") forms))
        names (assoc-in (ns-names nsf) [:aliases :self] (second nsf))
        defns (keep #(when (ck/defn-form? %) (defn-parts %)) forms)
        own (set (map :name defns))]
    (into {} (for [{nm :name params :params body :body} defns
                   :when (vector? params)]
               [nm (disj (into #{} (keep #(callee % own names)) (body-refs params body own))
                         nm)]))))

(defn call-graph
  "The call graph of a namespace, read from its source without loading
  it: {f #{g ...}} for each of its defns.  A callee is one of its own fns
  by simple name, or a fn of another namespace, qualified in full.
  clojure.core, host members and self-recursion are left out.  Effect
  code is read too; nothing here is checked."
  [ns-sym]
  (graph-of (book/read-forms (source-url ns-sym))))

(defn- check-calls
  "Each `calls` form against the target's call graph."
  [{:keys [target calls]} forms]
  (let [graph (graph-of forms)]
    (vec (for [[f gs] (sort-by (comp str first) calls)]
           (let [actual (get graph f)
                 unknown (first (filter #(and (nil? (namespace %)) (not (contains? graph %))) gs))]
             (cond
               (nil? actual)
               {:fn f :calls gs :status :failed
                :error (str "the spec gives `" f "` a call set, but " target " defines no fn `" f "`")}

               unknown
               {:fn f :calls gs :status :failed
                :error (str "the spec says `" f "` calls `" unknown "`, but " target
                            " defines no fn `" unknown "`")}

               :else
               (let [declared (set gs)
                     missing (vec (sort-by str (remove actual declared)))
                     extra (vec (sort-by str (remove declared actual)))]
                 (if (and (empty? missing) (empty? extra))
                   {:fn f :calls gs :status :ok}
                   {:fn f :calls gs :status :failed :missing missing :extra extra}))))))))

;; --- machines ----------------------------------------------------------------------

(defn- enum-values
  "Every value of type `t`, when it has only field-less constructors (or
  is Bool), in declaration order; nil otherwise."
  [t data]
  (cond
    (= 'Bool t) [true false]
    (symbol? t)
    (when-let [f (first (filter #(= t (second %)) data))]
      (let [ctors (remove vector? (drop 2 f))]
        (when (every? symbol? ctors)
          (mapv (fn [c] [(keyword (name c))]) ctors))))
    :else nil))

(defn- table-edges
  "[from event to] for each transition the table lists."
  [transitions]
  (for [[s evs] transitions, [ev t] evs] [s ev t]))

(defn- find-path
  "The shortest path of edges from `from` to `to`, never passing through
  `avoid`, as [[s ev t] ...]; nil when there is none.  A path has at least
  one edge."
  [edges from to avoid]
  (loop [frontier (mapv (fn [e] [e]) (filter #(= from (first %)) edges))
         seen #{from}]
    (when (seq frontier)
      (let [done (first (filter #(= to (nth (peek %) 2)) frontier))]
        (or done
            (let [nexts (for [path frontier
                              :let [t (nth (peek path) 2)]
                              :when (and (not (contains? seen t)) (not= t avoid))
                              e edges :when (= t (first e))]
                          (conj path e))]
              (recur (vec nexts) (into seen (map #(nth (peek %) 2) frontier)))))))))

(defn- reachable [edges from]
  (loop [todo [from], seen #{from}]
    (if-let [s (first todo)]
      (let [ts (remove seen (map #(nth % 2) (filter #(= s (first %)) edges)))]
        (recur (into (vec (rest todo)) ts) (into seen ts)))
      seen)))

(defn- show-path [path]
  (apply str (pr-str (first (first path)))
         (for [[_ ev t] path] (str " -" (pr-str ev) "-> " (pr-str t)))))

(defn- machine-domain
  "[states events] a machine's step is checked over."
  [[_ {:keys [step start transitions final states events]}] {:keys [anns data]}]
  (let [sig (get anns step)
        listed (distinct (concat [start] (keys transitions)
                                 (mapcat vals (vals transitions)) final))]
    [(vec (or states (enum-values (first (:params sig)) data) listed))
     (vec (or events (enum-values (second (:params sig)) data)
              (distinct (mapcat keys (vals transitions)))))]))

(defn- machine-prop
  "The machine's table as one closed proposition, so the adequacy check
  holds each stand-in for the step fn to it as it does to the laws."
  [[_ {:keys [step transitions]} :as m] e]
  (let [[states events] (machine-domain m e)]
    (cons 'and (for [s states, ev events]
                 (list '= (list step (list 'quote s) (list 'quote ev))
                       (list 'quote (get-in transitions [s ev] s)))))))

(defn- check-machine
  "Run the target's step fn over every state and event, against the table,
  then check the table against the machine's own constraints."
  [[nm {:keys [step start transitions final never before]} :as m] e target]
  (let [f (some-> (ns-resolve (the-ns target) step) deref)
        [states events] (machine-domain m e)
        mismatches (vec (for [s states, ev events
                              :let [listed? (contains? (get transitions s) ev)
                                    want (get-in transitions [s ev] s)
                                    got (try (f s ev) (catch Throwable t {:threw (ex-message t)}))]
                              :when (not= want got)]
                          (cond-> {:state s :event ev :expected want :actual got}
                            (not listed?) (assoc :unlisted true))))
        edges (table-edges transitions)
        from-start (reachable edges start)
        errors (vec (concat
                      (for [s states :when (not (contains? from-start s))]
                        (str (pr-str s) " cannot be reached from the start " (pr-str start)))
                      (when (seq final)
                        (for [s states
                              :when (and (contains? from-start s)
                                         (not-any? (reachable edges s) final))]
                          (str "from " (pr-str s) " no final state can be reached")))
                      (for [[a b] never
                            :let [p (find-path edges a b nil)]
                            :when p]
                        (str (pr-str a) " must never lead to " (pr-str b) ", but it does: "
                             (show-path p)))
                      (for [[a b] before
                            :let [p (when (not= start a) (find-path edges start b a))]
                            :when p]
                        (str (pr-str b) " must be reached only through " (pr-str a) ", but "
                             (show-path p) " avoids it"))))
        base {:machine nm :step step :states (count states) :events (count events)}]
    (if (and (empty? mismatches) (empty? errors))
      (assoc base :status :ok)
      (assoc base :status :failed
                  :mismatches (mapv #(dissoc % :unlisted) mismatches)
                  :shown (mapv (fn [{:keys [state event expected actual unlisted]}]
                                 (str "(" step " " (pr-str state) " " (pr-str event) ") is "
                                      (if (and (map? actual) (:threw actual))
                                        (str "a throw: " (:threw actual))
                                        (pr-str actual))
                                      ", but the table says " (pr-str expected)
                                      (when unlisted " (no transition listed: the state stays)")))
                               mismatches)
                  :errors errors))))

(defn- state-id [s]
  (let [id (-> (str/join "_" (map #(if (keyword? %) (name %) (str %)) (flatten [s])))
               (str/replace #"[^A-Za-z0-9_]" "_"))]
    (if (contains? #{"end" "state" "note"} id) (str id "_") id)))

(defn- state-diagram [{:keys [start transitions final]}]
  (str "stateDiagram-v2"
       "\n  [*] --> " (state-id start)
       (apply str (for [[s ev t] (table-edges transitions)]
                    (str "\n  " (state-id s) " --> " (state-id t) " : " (state-id ev))))
       (apply str (for [s final] (str "\n  " (state-id s) " --> [*]")))))

(defn- mermaid-id [s]
  (let [id (-> (str s) (str/replace "?" "_Q") (str/replace "!" "_B")
               (str/replace #"[^A-Za-z0-9_]" "_"))]
    (if (contains? #{"end" "graph" "subgraph" "flowchart"} id) (str id "_") id)))

(defn mermaid
  "A mermaid flowchart of a call graph.  Given a namespace, its own call
  graph.  Given a spec namespace, its target's (or opts :target's), with
  the spec's `calls` laid over it: a call the spec does not list is a
  dotted edge marked `not in spec`, and a call it lists that the code does
  not make is an edge marked `missing`."
  ([ns-sym] (mermaid ns-sym {}))
  ([ns-sym opts]
   (require ns-sym)
   (if-let [m (:machine opts)]
     (let [[_ spec-m] (or (first (filter #(= m (first %)) (:machines (get @registry ns-sym))))
                          (fail! "`" ns-sym "` has no machine `" m "`"))]
       (state-diagram spec-m))
   (let [e (get @registry ns-sym)
         target (if e (or (:target opts) (:target e)) ns-sym)
         graph (call-graph target)
         declared (into {} (map (fn [[f gs]] [f (set gs)])) (when e (:calls e)))
         edges (concat
                 (for [[f gs] (sort-by (comp str key) graph), g (sort-by str gs)]
                   (if (and (contains? declared f) (not (contains? (declared f) g)))
                     [f "-.->|not in spec|" g]
                     [f "-->" g]))
                 (for [[f gs] (sort-by (comp str key) declared)
                       g (sort-by str gs)
                       :when (and (contains? graph f) (not (contains? (get graph f) g)))]
                   [f "--x|missing|" g]))
         nodes (sort-by str (distinct (concat (keys graph) (mapcat (fn [[f _ g]] [f g]) edges))))]
     (str "flowchart LR"
          (apply str (for [n nodes] (str "\n  " (mermaid-id n) "[\"" n "\"]")))
          (apply str (for [[f arrow g] edges]
                       (str "\n  " (mermaid-id f) " " arrow " " (mermaid-id g)))))))))

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

(defn- format-failure [{:keys [law counterexample detail original trial seed error prover-bug proof]}]
  (let [pad (apply max 0 (map (comp count str) (keys counterexample)))]
    (str (when prover-bug
           (str "writ bug: law `" law "` was proved (" proof ") but a test refutes it; "
                "please report this with the seed below.\n"))
         "law `" law "` fails"
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
  [{:keys [ok target spec static laws gaps unspecified rejected calls machines proof]}]
  (str "writ.spec: " spec " against " target (if ok ": ok" ": FAILED")
       (when (and proof (pos? (:laws proof)))
         (str "\n  " (:proved proof) " of " (:laws proof) " laws proved"
              (when (= :proved (:require proof)) " (the spec requires proof)")
              (when-let [ts (seq (filter #(= :test (:evidence %)) laws))]
                (str "; tested, not proved: " (str/join ", " (map :law ts))))))
       (apply str (for [{l :law p :proof st :status} laws :when (= :proved st)]
                    (str "\n  law `" l "` proved " p)))
       (apply str (for [{l :law b :because} laws :when b]
                    (str "\n  law `" l "` is only tested: " b)))
       (when ok
         (apply str (for [{f :fn n :laws imps :rejected} rejected]
                      (str "\n  `" f "`: " n (if (= 1 n) " law, " " laws, ")
                           (count imps) " impostors rejected ("
                           (str/join ", " (for [[k c] (sort-by key (frequencies (map :kind imps)))]
                                            (str c " " (name k))))
                           ")"))))
       (when ok
         (apply str (for [{f :fn gs :calls} calls]
                      (str "\n  `" f "` "
                           (if (seq gs)
                             (str "calls exactly " (str/join ", " gs))
                             "calls nothing outside clojure.core")))))
       (when ok
         (apply str (for [{m :machine n :states k :events} machines]
                      (str "\n  machine `" m "`: " (* n k) " transitions checked"))))
       (when-not (:ok static) (str "\n\n" (:error static)))
       (apply str (for [{m :machine st :status :keys [shown errors step]} machines
                        :when (= :failed st)]
                    (str (when (seq shown)
                           (str "\n\nmachine `" m "`: `" step "` does not follow its table"
                                (apply str (map #(str "\n  " %) shown))))
                         (when (seq errors)
                           (str "\n\nmachine `" m "`: the table breaks its own constraints"
                                (apply str (map #(str "\n  " %) errors)))))))
       (apply str (for [{f :fn gs :calls :keys [error missing extra]} calls
                        :when (or error (seq missing) (seq extra))]
                    (if error
                      (str "\n\n" error)
                      (str "\n\nthe call graph of `" f "` is not the one the spec gives"
                           (apply str (for [g missing]
                                        (str "\n  `" f "` does not call `" g
                                             "`, which the spec says it calls")))
                           (apply str (for [g extra]
                                        (str "\n  `" f "` calls `" g
                                             "`, which the spec does not list")))
                           "\n  the spec says `" f "` calls "
                           (if (seq gs) (str "exactly " (str/join ", " gs)) "nothing outside clojure.core")
                           ". Call through the layers the spec names instead of around them."))))
       (apply str (map #(str "\n\n" (format-failure %)) (filter #(= :failed (:status %)) laws)))
       (apply str (for [{l :law why :unproved st :status need :require} laws :when (= :unproved st)]
                    (str "\n\nlaw `" l "` is tested, not proved, and the "
                         (if need "law" "spec") " requires proof"
                         "\n  the prover: " (or why "no proof found")
                         "\n  Prove it: state it in terms the prover models, or state the lemma"
                         "\n  it needs as a law of its own.  If it cannot be proved yet, say why"
                         "\n  on the law, and every report will show it:"
                         "\n  (law " l " {:require :tested :because \"...\"} ...)")))
       (apply str (map #(str "\n\nlaw `" (:law %) "` is vacuous: " (:why %)
                             ". A law must say what the code does.")
                       (filter #(= :vacuous (:status %)) laws)))
       (apply str (map (fn [{f :fn [s & more] :survivors}]
                         (str "\n\nthe spec does not pin down `" f "`: every law still holds when it "
                              s
                              (when (seq more)
                                (apply str (map #(str "\n  or when it " %) more)))
                              "\n  State what `" f "` must do, so that a law rejects this."))
                       gaps))
       (when (seq unspecified)
         (str "\n\nnot in the spec (no signature): " (str/join ", " unspecified)))))

(defn- thrown? [r]
  (or (:error r) (some (fn [[_ v]] (str/starts-with? (str v) "threw:")) (:detail r))))

(defn- prove-laws
  "Try to prove each law that ran.  A tested law the prover proves becomes
  :proved; a law it cannot prove keeps :tested with the reason.  A law
  that is proved yet refuted by a value (not a throw) is a writ bug."
  [results opts target spec-ns tenv anns]
  (if (= false (:prove opts))
    results
    (let [defs (delay (prover/definitions
                        [[target (book/read-forms (source-url target))]
                         [spec-ns (book/read-forms (source-url spec-ns))]]))]
      ;; a law proved here is a lemma for any law proved after it; one that
      ;; is only tested, or that a test refutes, never is.  Passes repeat
      ;; while they prove something new, so a law may cite one that comes
      ;; later in the spec, and no proof can lean on itself: each cites
      ;; only laws whose proofs were finished before it began
      (let [attempt (fn [r lemmas]
                      (try (let [[ds own] @defs]
                             (prover/prove-law {:prop (:prop r) :defs ds :tenv tenv
                                                :target target :own own :lemmas lemmas
                                                :rets (into {} (for [[nm sig] anns]
                                                                 [(symbol (str target) (str nm))
                                                                  (plain (:ret sig))]))}))
                           (catch Throwable e
                             {:proved false :reason (str "the prover failed: " (ex-message e))})))
            open? (fn [r] (and (:prop r) (contains? #{:tested :failed} (:status r))
                               (not (:proof r)) (not (:unproved-final r))))
            pass (fn [[rs lemmas]]
                   (reduce
                     (fn [[out lemmas] r]
                       (if-not (open? r)
                         [(conj out r) lemmas]
                         (let [pr (attempt r lemmas)]
                           (cond
                             (and (:proved pr) (= :tested (:status r)))
                             [(conj out (cond-> (-> r (dissoc :unproved)
                                                    (assoc :status :proved :proof (:summary pr)))
                                          (seq (:lemmas pr)) (assoc :lemmas (:lemmas pr))))
                              (conj lemmas {:name (:law r) :prop (:prop r)})]

                             (and (:proved pr) (not (thrown? r)))
                             [(conj out (assoc r :prover-bug true :proof (:summary pr))) lemmas]

                             (= :tested (:status r))
                             [(conj out (cond-> (assoc r :unproved (:reason pr))
                                          ;; outside the model: no lemma changes that
                                          (str/starts-with? (str (:reason pr)) "outside")
                                          (assoc :unproved-final true)))
                              lemmas]
                             :else [(conj out (assoc r :unproved-final true)) lemmas]))))
                     [[] lemmas]
                     rs))]
        (loop [[rs lemmas] (pass [results []])]
          (let [[rs2 lemmas2] (pass [rs lemmas])]
            (if (= (count lemmas2) (count lemmas))
              (mapv #(dissoc % :unproved-final) rs2)
              (recur [rs2 lemmas2]))))))))

(def ^:private evidence-of
  {:proved :proof, :evaluated :proof, :witnessed :proof, :tested :test})

(defn- require-evidence
  "Mark each law with the evidence it got (:proof or :test) and what it
  needed.  A law that needs proof and was only tested is :unproved."
  [results laws level]
  (let [opts (into {} (map (juxt :name :opts)) laws)]
    (mapv (fn [r]
            (let [o (get opts (:law r))
                  need (or (:require o) level)
                  ev (evidence-of (:status r))
                  r (cond-> (merge r (select-keys o [:require :because]))
                      ev (assoc :evidence ev))]
              (if (and (= :proved need) (= :test ev))
                (assoc r :status :unproved)
                r)))
          results)))

(defn- proof-coverage [results level]
  {:require level
   :proved (count (filter #(= :proof (:evidence %)) results))
   :tested (count (filter #(= :test (:evidence %)) results))
   :laws (count results)})

(defn check
  "Check a spec namespace against its target (or opts :target).  Returns a
  report map; :ok says whether everything held and :message explains any
  failure.  opts: :target, :trials (test.check runs per law, default 100),
  :seed (default random; each law's report carries the one it used) and
  :max-size (the largest generated size, default 50), :adequacy (false
  skips the gap check), :prove (false skips the prover) and :require
  (:proved or :tested, in place of the spec's own)."
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
       (let [r (assoc base :ok false :laws [] :gaps [] :calls [] :machines [])]
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
                                (let [qp (qualify p #{} publics interns target spec-ns)]
                                  (cond
                                    (not (calls-target? qp target))
                                    {:law name :status :vacuous
                                     :why (str "it calls no fn of " target)}

                                    (try-prove p tenv opaque numeric-fns)
                                    {:law name :status :vacuous
                                     :why (str "writ.norm proves it without looking at the "
                                               "implementation, so any code satisfies it")}

                                    :else
                                    (assoc (test-law ctx {:name name :prop qp}
                                                     {:trials trials :seed seed :max-size max-size})
                                           :prop qp)))
                                ;; a law that cannot be run (a malformed
                                ;; proposition, a type with no generator)
                                ;; fails with the reason, not the whole check
                                (catch Throwable ex
                                  {:law name :status :failed :counterexample {} :detail []
                                   :error (or (ex-message ex) (str ex))}))))
                       (finally (unwrap! wrapped)))
             level (or (:require opts) (:require e) :tested)
             _ (check-level! "`check`" level)
             results (-> (prove-laws results opts target spec-ns tenv anns)
                         (require-evidence laws level))
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
             sound? (not-any? #(contains? #{:failed :vacuous} (:status %)) results)
             per-fn (if (and sound? (not= false (:adequacy opts)))
                      (adequacy ctx target
                                (sort (filter #(contains? publics %) (keys anns)))
                                anns (concat (keep :prop results)
                                             (for [m (:machines e)]
                                               (qualify (machine-prop m e) #{} publics interns
                                                        target spec-ns)))
                                trials (or seed 42))
                      [])
             gaps (vec (for [{f :fn s :survivors} per-fn :when (seq s)]
                         {:fn f :survivors s}))
             results (mapv #(dissoc % :prop) results)
             call-results (check-calls e (book/read-forms (source-url target)))
             machine-results (mapv #(check-machine % e target) (:machines e))
             r (assoc base :laws results :gaps gaps :calls call-results
                           :proof (proof-coverage results level)
                           :machines (mapv #(dissoc % :shown :step) machine-results)
                           :rejected (mapv #(select-keys % [:fn :laws :rejected]) per-fn)
                           :ok (and sound? (empty? gaps)
                                    (not-any? #(= :unproved (:status %)) results)
                                    (every? #(= :ok (:status %)) call-results)
                                    (every? #(= :ok (:status %)) machine-results)))]
         (assoc r :message (format-report (assoc r :machines machine-results))))))))

(defn check!
  "`check`, throwing with the report's message when anything fails."
  ([spec-ns] (check! spec-ns {}))
  ([spec-ns opts]
   (let [r (check spec-ns opts)]
     (if (:ok r)
       r
       (throw (ex-info (:message r) {:writ/error true :report r}))))))
