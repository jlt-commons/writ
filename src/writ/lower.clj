(ns writ.lower
  "Lower macroexpanded Clojure core forms into writ's core AST.

  The AST is small and structural:

    {:op :ref    :name sym}
    {:op :lit    :val v}
    {:op :if     :test :then :else}
    {:op :do     :stmts [...] :ret t}
    {:op :let    :bindings [[bform init] ...] :body t}
    {:op :loop   :bindings [[name init] ...] :body t}
    {:op :recur  :args [...]}
    {:op :fn     :name sym|nil :params [sym ...] :body t}
    {:op :case   :scrut t :clauses [{:test lit :body t}] :default t}
    {:op :invoke :fn t :args [t ...]}")

(declare lower)

(def ^:dynamic *locals*
  "Unqualified names bound around the form being lowered: the book's own
  top-level names, the defn's params, and every local binder in scope.
  Ported from typed.clj.analyzer's macroexpand-1: locals shadow macros, so
  a head bound here is an ordinary call and is never macroexpanded."
  #{})

(def effect-names
  "clojure.core fns and macros that are not pure data-and-functions code:
  eval and the load family, namespace and var mutation, reference state,
  concurrency, console/file I/O and randomness.  The hosts run them fine;
  writ owns the purity contract statically."
  '#{eval load load-file load-string load-reader
     require use import refer refer-clojure in-ns create-ns remove-ns
     ns-unmap ns-unalias alias intern
     alter-var-root with-redefs with-redefs-fn binding with-bindings
     with-bindings* push-thread-bindings pop-thread-bindings var-set
     alter-meta! reset-meta! set-validator! add-watch remove-watch
     atom swap! swap-vals! reset! reset-vals! compare-and-set!
     volatile! vreset! vswap!
     future future-call future-cancel promise deliver
     agent send send-off send-via await await-for restart-agent
     shutdown-agents release-pending-sends
     dosync sync ref ref-set alter commute ensure io! locking
     pmap pcalls pvalues
     print println pr prn printf newline flush read read-line slurp spit
     rand rand-int rand-nth shuffle random-uuid random-sample
     extend extend-type extend-protocol requiring-resolve
     tap> add-tap remove-tap with-open time
     resolve ns-resolve ns-publics ns-interns ns-map ns-refers ns-aliases
     ns-imports find-var find-ns all-ns the-ns})

(def interop-names
  "clojure.core macros that build host classes: they are interop, like
  typed.clj.analyzer's reify*/deftype* specials they expand to."
  '#{reify proxy proxy-super gen-class gen-interface})

(defn host-member?
  "A static member of a host class, written `Class/member`: `System/getenv`,
  `Math/abs`, `java.lang.Math/PI`.  It lowers to a qualified ref, the same
  shape as a call into another namespace, so it is told apart by its
  qualifier: a class name's last segment starts with a capital letter, and a
  Clojure namespace's does not."
  [s]
  (and (symbol? s)
       (some? (namespace s))
       (boolean (re-find #"(?:^|\.)[A-Z][^.]*$" (namespace s)))))

(defn effect-head?
  "An effect or interop name as written in call position:
  clojure.core-qualified, or unqualified and not shadowed by a book name
  or local."
  [h locals]
  (and (symbol? h)
       (let [n (symbol (name h))]
         (or (contains? effect-names n) (contains? interop-names n)))
       (or (= "clojure.core" (namespace h))
           (and (nil? (namespace h)) (not (contains? locals h))))))

(defn binding-names
  "Every name a binding form introduces: a symbol, `[a b]`, or `{:keys [a b] :as m}`."
  [bform]
  (cond
    (symbol? bform) [bform]
    (vector? bform) (vec (mapcat binding-names bform))
    (map? bform)    (vec (mapcat binding-names
                                 (mapcat (fn [[k v]] (if (#{:keys :strs :syms} k) [v] []))
                                         bform)))
    :else []))

(defn valid-binding-symbol?
  "A binding symbol is a simple symbol: no namespace, no dots.  Ported
  from typed.cljc.analyzer, which enforces it for every binder the
  compiler checks (fn params, let/loop bindings, catch binders, letfn
  names); writ's host is lax here, so the contract is writ's to own."
  [s]
  (and (symbol? s)
       (not (namespace s))
       (not (re-find #"\." (name s)))))

(defn- bad-binding!
  [b what]
  (throw (ex-info (str "Writ: Bad binding form: `" b "`; " what
                       " must be a simple symbol")
                  {:writ/error true :binder b})))

(defn pattern-overlap
  "Why a destructuring pattern copies its source, or nil.  Destructuring
  consumes the source like a match: each binder takes a distinct piece, so
  two binders over the same key, or `:as` beside any other binder, copy
  it."
  [pat]
  (cond
    (vector? pat)
    (let [as? (some #{:as} pat)
          elems (loop [ps (seq pat), acc []]
                  (cond
                    (empty? ps) acc
                    (= :as (first ps)) (recur (nnext ps) acc)
                    (= '& (first ps)) (recur (nnext ps) (conj acc (second ps)))
                    :else (recur (next ps) (conj acc (first ps)))))]
      (or (some pattern-overlap elems)
          (when (and as? (seq elems))
            "`:as` binds the whole value beside its elements")))

    (map? pat)
    (let [ns-key (fn [k s kind]
                   (let [n (name s)
                         nsp (or (namespace s) (when (keyword? k) (namespace k)))]
                     (case kind
                       :keys (keyword nsp n)
                       :strs n
                       :syms (list 'quote (symbol nsp n)))))
          projected (mapcat (fn [[k v]]
                              (cond
                                (and (keyword? k)
                                     (contains? #{"keys" "strs" "syms"} (name k)))
                                (map #(ns-key k % (keyword (name k))) v)
                                (or (= :as k) (= :or k)) []
                                :else [v]))
                            pat)
          nested (keep (fn [[k _]] (when (or (vector? k) (map? k)) k)) pat)
          dup (first (filter #(> (val %) 1) (frequencies projected)))]
      (or (some pattern-overlap nested)
          (when dup (str "two binders read the key " (pr-str (key dup))))
          (when (and (contains? pat :as) (seq projected))
            "`:as` binds the whole value beside its fields")))

    :else nil))

(defn- destructure-bindings
  "Expand a binding vector with clojure.core/destructure, which compiles
  :as, &, keys/strs/syms and nesting into plain sequential lets and
  preserves binder metadata."
  [bvec]
  (let [d (clojure.core/destructure bvec)]
    (mapv (fn [i]
            (let [b (nth d (* 2 i))]
              (when-not (valid-binding-symbol? b)
                (bad-binding! b "a let/loop binder"))
              [b (nth d (inc (* 2 i)))]))
          (range (quot (count d) 2)))))

(defn- param-syms [params]
  (when-not (vector? params)
    (throw (ex-info (if (and (sequential? params) (seq params)
                             (vector? (first params)))
                      "Writ: a multi-arity `fn` is not supported; writ checks a single arity"
                      "Writ: a parameter declaration requires a vector of parameters")
                    {:writ/error true})))
  (let [ri (first (keep-indexed (fn [i p] (when (= '& p) i)) params))]
      (when (and (some? ri)
                 (or (= ri (dec (count params)))
                     (not (symbol? (get params (inc ri))))
                     (= '& (get params (inc ri)))
                     (> (count params) (+ ri 2))))
        (throw (ex-info "Writ: a rest parameter must be followed by exactly one rest name"
                        {:writ/error true})))
      (mapv (fn [p]
              (cond
                (nil? p) p
                (valid-binding-symbol? p) p
                (symbol? p) (bad-binding! p "a parameter")
                :else (throw (ex-info "Writ: only simple parameter symbols are supported"
                                      {:writ/error true :param p}))))
            (remove #{'&} params))))

(defn- arity-of-params
  "{:min :max} for a raw parameter vector; a nil max means variadic.
  Attached to every fn node so call sites can check arity without
  re-deriving it."
  [params]
  (let [ri (first (keep-indexed (fn [i p] (when (= '& p) i)) params))]
    (if (some? ri)
      {:min ri :max nil}
      {:min (count params) :max (count params)})))

(defn- lower-do [forms]
  (cond
    (empty? forms) {:op :lit :val nil}
    (= 1 (count forms)) (lower (first forms))
    :else {:op :do :stmts (mapv lower (butlast forms)) :ret (lower (last forms))}))

(defn plain-params
  "A parameter vector with each destructuring pattern replaced by a fresh
  name, and the body wrapped in a let that takes the pattern apart, which
  is what clojure.core/fn does: [[params] body].  The fresh name keeps the
  pattern's metadata, so a type given to the pattern types it."
  [params body]
  (if (or (not (vector? params))
          (every? #(or (symbol? %) (nil? %)) params))
    [params body]
    (let [ps (mapv #(if (or (symbol? %) (nil? %)) % (with-meta (gensym "p__") (meta %))) params)
          binds (vec (mapcat (fn [p q] (when-not (= p q) [p q])) params ps))]
      [ps (list (list* 'let binds body))])))

(defn- lower-fn [form]
  ;; (fn name? [params] body...) -- name, params and body each optional in
  ;; position; an unnamed fn still has its params and body.
  (let [tail (rest form)
        [nm tail] (if (symbol? (first tail)) [(first tail) (rest tail)] [nil tail])
        [params body] (plain-params (first tail) (rest tail))]
    (let [ps (param-syms params)]
      {:op :fn
       :name nm
       :params ps
       :writ/arity (arity-of-params params)
       :body (binding [*locals* (into (cond-> *locals* nm (conj nm))
                                      (remove nil?) ps)]
               (lower-do body))})))

(defn- lower-bindings
  "Lower destructured binding pairs in order: each init sees the binders
  before it, and the body sees them all."
  [pairs body]
  (loop [ps pairs, locals *locals*, acc []]
    (if (seq ps)
      (let [[b init] (first ps)]
        (recur (rest ps) (conj locals b)
               (conj acc [b (binding [*locals* locals] (lower init))])))
      [acc (binding [*locals* locals] (lower-do body))])))

(defn- overlaps
  "[init why] for each binding pair whose pattern copies its init."
  [bvec]
  (vec (keep (fn [[b init]] (when-let [why (pattern-overlap b)] [init why]))
             (partition 2 bvec))))

(defn- lower-let [form]
  (let [[_ bvec & body] form
        _ (when-not (vector? bvec)
            (throw (ex-info
                     (str "Writ: `" (name (first form))
                          "` requires a vector for its bindings, had: " (class bvec))
                     {:writ/error true})))
        [pairs body-ast] (lower-bindings (destructure-bindings bvec) body)]
    (cond-> {:op :let :bindings pairs :body body-ast}
      (seq (overlaps bvec)) (assoc :writ/overlaps (overlaps bvec)))))

(defn- lower-letfn [form]
  ;; (letfn [(f [ps] body) ...] body...) -- each spec becomes a let pair
  ;; bound to the equivalent named fn
  (let [[_ specs & body] form
        _ (when-not (vector? specs)
            (throw (ex-info "Writ: `letfn` requires a vector of fn specs"
                            {:writ/error true})))
        _ (doseq [spec specs]
            (when-not (and (sequential? spec)
                           (>= (count spec) 2)
                           (symbol? (first spec))
                           (vector? (second spec)))
              (throw (ex-info "Writ: a `letfn` spec must be `(name [params] body*)`"
                              {:writ/error true})))
            (when-not (valid-binding-symbol? (first spec))
              (bad-binding! (first spec) "a letfn name")))
        pairs (mapcat (fn [spec] [(first spec) (apply list 'fn* spec)]) specs)]
    ;; every spec name is in scope in every spec and the body
    (binding [*locals* (into *locals* (map first) specs)]
      (lower-let (apply list 'let (vec pairs) body)))))

(defn- lower-try [form]
  ;; (try body* (catch C b body*)* (finally expr*)?) -- the body and the
  ;; catch arms are exclusive paths, so they lower to an `if` on a literal
  ;; and join; `finally` runs on every path, so its uses are sequenced into
  ;; both branches (join takes the max, so a finally use still counts once
  ;; per path against the branch it shares)
  (let [tail (rest form)
        clause? (fn [c nm] (and (seq? c) (symbol? (first c)) (= nm (name (first c)))))
        _ (loop [ts tail seen-catch? false seen-fin? false]
            (when (seq ts)
              (let [t (first ts)]
                (cond
                  (and seen-fin? (clause? t "finally"))
                  (throw (ex-info "Writ: Only one finally clause allowed in try expression"
                                  {:writ/error true}))
                  seen-fin?
                  (throw (ex-info "Writ: the `finally` clause must be last in a `try`"
                                  {:writ/error true}))
                  (clause? t "catch")
                  (do (when (or (< (count t) 3)
                                (not (symbol? (second t)))
                                (not (symbol? (nth t 2))))
                        (throw (ex-info "Writ: a catch clause must be `(catch Class binder body*)`"
                                        {:writ/error true})))
                      (when-not (valid-binding-symbol? (nth t 2))
                        (bad-binding! (nth t 2) "a catch binder"))
                      (recur (rest ts) true seen-fin?))
                  (clause? t "finally") (recur (rest ts) seen-catch? true)
                  seen-catch?
                  (throw (ex-info "Writ: only catch or finally clauses can follow a catch in a `try`"
                                  {:writ/error true}))
                  :else (recur (rest ts) seen-catch? seen-fin?)))))
        body (remove #(or (clause? % "catch") (clause? % "finally")) tail)
        catches (filter #(clause? % "catch") tail)
        fins (filter #(clause? % "finally") tail)
        fin-asts (mapv lower (mapcat rest fins))
        wrap (fn [t] (if (seq fin-asts) {:op :do :stmts fin-asts :ret t} t))
        lower-catch (fn [c]
                      (let [[_ _ binder & cbody] c]
                        {:op :let :bindings [[binder {:op :lit :val nil}]]
                         :body (binding [*locals* (conj *locals* binder)]
                                 (lower-do cbody))}))
        else-ast (wrap (reduce (fn [acc c] {:op :if :test {:op :lit :val true}
                                             :then (lower-catch c) :else acc})
                                {:op :lit :val nil}
                                (reverse catches)))]
    {:op :if :writ/try? true :test {:op :lit :val true}
            :then (wrap (lower-do body))
            :else else-ast}))

(defn- lower-loop [form]
  (let [[_ bvec & body] form
        _ (when-not (vector? bvec)
            (throw (ex-info
                     (str "Writ: `" (name (first form))
                          "` requires a vector for its bindings, had: " (class bvec))
                     {:writ/error true})))
        [pairs body-ast] (lower-bindings (destructure-bindings bvec) body)]
    (cond-> {:op :loop :bindings pairs :body body-ast}
      (seq (overlaps bvec)) (assoc :writ/overlaps (overlaps bvec)))))

(defn- lower-case [form]
  ;; (case e c1 v1 c2 v2 ... default?)
  ;; an even tail is all clauses; an odd tail's last item is the default
  (let [_ (when (< (count form) 2)
            (throw (ex-info
                     (str "Writ: Wrong number of args to case, had: " (- (count form) 1))
                     {:writ/error true})))
        _ (when (= (count form) 2)
            (throw (ex-info "Writ: `case` requires at least one clause or a default"
                            {:writ/error true})))
        scrut (second form)
        tail (drop 2 form)
        default? (odd? (count tail))
        pairs (partition 2 (if default? (butlast tail) tail))
        default (when default? (last tail))]
    {:op :case
     :scrut (lower scrut)
     :clauses (mapv (fn [[c b]] {:test c :body (lower b)}) pairs)
     ;; a false or nil default is still a default
     :default (when default? (lower default))}))

(defn lower [form]
  (cond
    (symbol? form) {:op :ref :name form}
    ;; `()` is the empty list, a literal, not a call
    (and (seq? form) (empty? form)) {:op :lit :val ()}
    (seq? form)
    (let [h (first form)]
      (cond
        ;; locals shadow macros (t.c. macroexpand-1); special forms cannot
        ;; be shadowed.  An effect head is kept whole so the effect gate
        ;; sees the name as written, not its expansion.
        (or (and (symbol? h) (nil? (namespace h)) (contains? *locals* h)
                 (not (special-symbol? h)))
            (effect-head? h *locals*))
        {:op :invoke :fn (lower h) :args (mapv lower (rest form))}

        :else
      (case h
        (fn fn* clojure.core/fn)     (lower-fn form)
        (let let* clojure.core/let)  (lower-let form)
        (letfn letfn* clojure.core/letfn clojure.core/letfn*) (lower-letfn form)
        (try clojure.core/try)       (lower-try form)
        (loop loop* clojure.core/loop) (lower-loop form)
         (if clojure.core/if)         (let [fc (count form)]
                                       (when-not (or (= fc 3) (= fc 4))
                                         (throw (ex-info
                                                  (str "Writ: Wrong number of args to if, had: " (- fc 1))
                                                  {:writ/error true})))
                                       {:op :if :test (lower (second form))
                                        :then (lower (nth form 2))
                                        :else (lower (nth form 3 nil))})
        (do clojure.core/do)         (lower-do (rest form))
        (recur clojure.core/recur)   {:op :recur :args (mapv lower (rest form))}
        (case clojure.core/case)     (lower-case form)
        (unquote clojure.core/unquote)
        (throw (ex-info "Writ: Unsupported special form: unquote"
                        {:writ/error true}))

        (unquote-splicing clojure.core/unquote-splicing)
        (throw (ex-info "Writ: Unsupported special form: unquote-splicing"
                        {:writ/error true}))

        (quote clojure.core/quote)   (let [fc (count form)]
                                       (when-not (= fc 2)
                                         (throw (ex-info
                                                  (str "Writ: Wrong number of args to quote, had: " (dec fc))
                                                  {:writ/error true})))
                                       {:op :lit :val (second form)})
        ;; cond takes test/expr pairs: an odd tail is a compile error on
        ;; the JVM ("cond requires an even number of forms"); jolt's cond
        ;; macro crashes instead, so the guard lives before expansion
        (cond clojure.core/cond)
        (let [clauses (rest form)]
          (when (odd? (count clauses))
            (throw (ex-info "Writ: cond requires an even number of forms"
                            {:writ/error true})))
          (lower (macroexpand-1 form)))
        (cond-> clojure.core/cond-> cond->> clojure.core/cond->>)
        (let [clauses (drop 2 form)]
          (when (odd? (count clauses))
            (throw (ex-info "Writ: cond requires an even number of forms"
                            {:writ/error true})))
          (lower (macroexpand-1 form)))
        (let [ex (macroexpand-1 form)]
          (if (identical? ex form)
            {:op :invoke :fn (lower h) :args (mapv lower (rest form))}
            (lower ex))))))
    :else (cond
            (vector? form) {:op :vec :items (mapv lower form)}
            (map? form)    {:op :map :keys (mapv lower (keys form))
                                     :vals (mapv lower (vals form))}
            (set? form)    {:op :set :items (mapv lower form)}
            :else {:op :lit :val form})))

;; --- uniquify --------------------------------------------------------------
;;
;; Rename every binder to a fresh name so sibling scopes cannot collide --
;; tools.analyzer's uniquify-locals, the pass Typed Clojure runs before
;; checking.  After destructure, let/loop binder forms are plain symbols.
;; References are renamed along; metadata (quantities) survives.

(def ^:private !ctr (atom 0))

(defn- fresh-sym [n]
  (when (symbol? n)
    (with-meta (symbol (str (name n) "__" (swap! !ctr inc))) (meta n))))

(declare uniq)

(defn- uniq-bindings [pairs env]
  (loop [ps pairs, env env, acc []]
    (if (seq ps)
      (let [[b init] (first ps)
            init* (uniq init env)
            b* (fresh-sym b)
            env* (if b* (assoc env b b*) env)]
        (recur (rest ps) env* (conj acc [b* init*])))
      [(vec acc) env])))

(defn- uniq [ast env]
  (case (:op ast)
    :ref (if-let [r (get env (:name ast))] (assoc ast :name r) ast)
    :fn (let [nm* (fresh-sym (:name ast))
              env* (cond-> env
                     nm* (assoc (:name ast) nm*))
              ps (keep fresh-sym (:params ast))
              env* (into env* (map vector (remove nil? (:params ast)) ps))]
          (assoc ast :name nm*
                     :params (vec (mapv (fn [p p*] (if p* p* p)) (:params ast) (concat ps (repeat nil))))
                     :body (uniq (:body ast) env*)))
    (:let :loop) (let [[bs env*] (uniq-bindings (:bindings ast) env)]
                   (assoc ast :bindings bs :body (uniq (:body ast) env*)))
    :if (assoc ast :test (uniq (:test ast) env)
                   :then (uniq (:then ast) env)
                   :else (uniq (:else ast) env))
    :do (assoc ast :stmts (mapv #(uniq % env) (:stmts ast))
                :ret (uniq (:ret ast) env))
    :invoke (assoc ast :fn (uniq (:fn ast) env)
                       :args (mapv #(uniq % env) (:args ast)))
    :recur (assoc ast :args (mapv #(uniq % env) (:args ast)))
    :case (assoc ast :scrut (uniq (:scrut ast) env)
                     :clauses (mapv (fn [c] (assoc c :body (uniq (:body c) env))) (:clauses ast))
                     :default (when (:default ast) (uniq (:default ast) env)))
    :vec (assoc ast :items (mapv #(uniq % env) (:items ast)))
    :set (assoc ast :items (mapv #(uniq % env) (:items ast)))
    :map (assoc ast :keys (mapv #(uniq % env) (:keys ast))
                    :vals (mapv #(uniq % env) (:vals ast)))
    ast))

(defn uniquify
  "Rename every binder in a lowered AST to a fresh, unique name, renaming
  references along and preserving binder metadata."
  [ast]
  (uniq ast {}))
