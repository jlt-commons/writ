(ns writ.prove.translate
  "Turn Clojure into prover terms.

  Definitions and law terms are lowered by writ.lower (so cond, when,
  if-let, and, or and destructuring are already let and if), then read
  into terms.  Only the fragment the rewrite rules model is accepted:
  anything else -- a core fn not in `core-fns`, conj onto a value not
  known to be a vector, host calls, named or variadic local fns, a
  computed value called as a fn -- raises `outside`, and a law that
  needs it is left to testing.  A
  loop becomes a recursive definition of its own, over its bindings and
  the locals it closes over, and recur a call of it."
  (:require [writ.lower :as l]
            [writ.prove.term :as t]))

(def core-fns
  "The clojure.core fns the prover models."
  '#{seq first rest next second empty? count cons list vector vec concat
     filter map not = not= < <= > >= + - * inc dec zero? pos? neg? nth identity apply
     reduce integer? max min abs every? some quot mod rem contains? boolean
     bit-shift-left bit-shift-right set hash-set into mapcat
     sort sort-by distinct reverse last butlast take drop str name keyword
     vector? sequential? map? get nil? some?
     keyword? symbol? string? char? boolean?
     hash-map assoc dissoc merge keys vals get-in assoc-in update update-in
     subvec mapv filterv keep remove not-any? range conj number? fn?
     complement comp key val even? odd? map-indexed repeat true? false? merge-with zipmap})

(def ^:private vector-fns
  "The clojure.core fns whose value is always a vector."
  '#{vec mapv filterv subvec vector})

(defn- vector-term?
  "Is term t, as translated, a vector: a vector literal, a call of a fn
  that makes one, conj or into onto one, or an if of two?"
  [t]
  (boolean (or (:vector (meta t))
               (and (= :if (t/head t)) (vector-term? (nth t 2)) (vector-term? (nth t 3))))))

(def value-fns
  "The clojure.core fns that may be passed as values: the modelled ones,
  and pure predicates the prover keeps opaque."
  (-> core-fns (disj 'conj) (into '#{odd? even? nil? some? true? false?})))

(defn outside!
  "Signal a form the prover does not model."
  [what]
  (throw (ex-info (str "outside the prover: " what) {::outside what})))

(defn outside-reason [ex] (::outside (ex-data ex)))

(defn- scalar? [x]
  (or (nil? x) (number? x) (string? x) (keyword? x) (char? x) (boolean? x) (symbol? x)))

(defn- plain-data?
  "A scalar, a sequential or a map of plain data, or a set of scalars."
  [x]
  (or (scalar? x)
      (and (sequential? x) (every? plain-data? x))
      (and (map? x) (every? plain-data? (keys x)) (every? plain-data? (vals x)))
      (and (set? x) (every? scalar? x))))

(defn- constant
  "The value of a def the name refers to, when it is plain data the prover
  can hold: a scalar, a sequential of plain data, or a set of scalars.  Code is pure, so a
  def's value is fixed once its namespace is loaded; nil otherwise."
  [ctx s]
  (let [v (try (if (namespace s)
                 (resolve s)
                 (some-> (:ns ctx) find-ns (ns-resolve s)))
               (catch Throwable _ nil))]
    (when (and (var? v) (bound? v) (not (:dynamic (meta v))))
      (let [x @v]
        (when (plain-data? x)
          [x])))))

(defn- member-set
  "The set of scalars a contains? tests against, when the AST names one: a
  set literal, or a def holding one."
  [ctx env ast]
  (case (:op ast)
    :lit (when (and (set? (:val ast)) (every? scalar? (:val ast))) (:val ast))
    :set (when (every? #(and (= :lit (:op %)) (scalar? (:val %))) (:items ast))
           (set (map :val (:items ast))))
    :ref (when-not (or (contains? env (:name ast)) (contains? (:own ctx) (:name ast)))
           (when-let [[x] (constant ctx (:name ast))] (when (set? x) x)))
    nil))

(defn- fresh [ctx base]
  (symbol (str base "%" (swap! (:counter ctx) inc))))

(declare term-of)

(def ^:private taking-apart
  "Core fns that only take a value apart or measure it: on a value of the
  type the static check gives it they return, and destructuring is made of
  them."
  '#{get nth first second rest next seq key val count})

(defn- always-read?
  "Does evaluating AST node ast read local b on every path: b itself, a
  test of an if, an argument of a call, a binding's init, or both branches
  of an if?  A fn literal's body is not run where it is written."
  [b ast]
  (case (:op ast)
    :ref (= b (:name ast))
    :if (or (always-read? b (:test ast))
            (and (always-read? b (:then ast)) (always-read? b (:else ast))))
    :invoke (or (always-read? b (:fn ast)) (some #(always-read? b %) (:args ast)))
    :let (or (some (fn [[_ init]] (always-read? b init)) (:bindings ast)) (always-read? b (:body ast)))
    :do (or (some #(always-read? b %) (:stmts ast)) (always-read? b (:ret ast)))
    (:vector :set) (boolean (some #(always-read? b %) (:items ast)))
    false))

(defn- strictly
  "body, after init has run: (strict init body), or body when init is a
  value, or a taking apart of one, that cannot throw."
  [init body]
  (if (or (symbol? init) (contains? #{:lit :nil :fn :cfn :dfn :sq} (t/head init))
          (and (= :call (t/head init)) (contains? taking-apart (second init))
               (or (not= 'nth (second init)) (= 5 (count init)))
               (every? #(or (symbol? %) (contains? #{:lit :nil} (t/head %))
                            (and (= :call (t/head %)) (contains? taking-apart (second %))))
                       (drop 2 init))))
    body
    [:call 'writ.prove.term/strict init body]))

(defn- call-head
  "How a call's head is read: [:local term], [:own qualified], [:core sym]."
  [ctx env s]
  (cond
    (contains? env s) [:local (get env s)]
    (contains? (:own ctx) s) [:own (get (:own ctx) s)]
    ;; writ's own =, with NaN the same as NaN
    (contains? '#{same writ.spec/same writ.prove.term/same} s) [:core 'writ.prove.term/same]
    (and (contains? #{nil "clojure.core"} (namespace s))
         (contains? core-fns (symbol (name s)))) [:core (symbol (name s))]
    ;; the set operations, as the prover reads sets: by membership
    (and (= "clojure.set" (namespace s)) (contains? '#{intersection union difference} (symbol (name s))))
    [:core (symbol (str "set-" (name s)))]
    :else nil))

(defn- case-term [ctx env {:keys [scrut clauses default]}]
  (let [s (term-of ctx env scrut)
        test-of (fn [c] [:call '= s (t/value->term c)])]
    (reduce (fn [else {:keys [test body]}]
              (let [cs (if (seq? test) test [test])
                    cond-term (reduce (fn [acc c] [:if (test-of c) [:lit true] acc])
                                      [:lit false] (reverse cs))]
                [:if cond-term (term-of ctx env body) else]))
            (if default (term-of ctx env default) [:bottom])
            (reverse clauses))))

(defn- invoke-term [ctx env f args]
  (case (:op f)
    :ref (let [[k v] (call-head ctx env (:name f))]
           (case k
             :local (into [:ap v] args)
             :own (into [:app v] args)
             :core (let [a (first args)]
                     (cond
                       (contains? vector-fns v) (with-meta (into [:call v] args) {:vector true})
                       ;; conj and into add at the end of a vector: to the
                       ;; model, its elements then theirs
                       (and (= 'conj v) (seq (rest args)) (vector-term? a))
                       (with-meta [:sq (reduce (fn [e x] [:eapp e [:econs x t/enil]]) [:elems a] (rest args))]
                         {:vector true})
                       (= 'conj v) (outside! "conj onto a value not known to be a vector")
                       (and (= 'into v) (= 2 (count args)) (vector-term? a))
                       (with-meta [:sq [:eapp [:elems a] [:elems (second args)]]] {:vector true})
                       :else (into [:call v] args)))
             (if-let [[x] (when-not (contains? env (:name f)) (constant ctx (:name f)))]
               ;; a def of a map or a set, called as a fn: a lookup
               (if (and (or (map? x) (set? x)) (<= 1 (count args) 2))
                 (into [:call 'get (if (set? x)
                                     (into [:call 'hash-set] (map t/lit (t/sort-printed x)))
                                     (t/value->term x))]
                       args)
                 (outside! (str "`" (:name f) "`")))
               (outside! (str "`" (:name f) "`")))))
    :fn (into [:ap (term-of ctx env f)] args)
    ;; (:k m) and (:k m default) are lookups
    :lit (if (and (keyword? (:val f)) (<= 1 (count args) 2))
           (into [:call 'get (first args) [:lit (:val f)]] (rest args))
           (outside! "calling a computed value"))
    (outside! "calling a computed value")))

(defn- self-calls-without
  "t with each call of loop q, which takes n bindings then m closed-over
  locals, passing only the locals at the indexes in kept."
  [q n m kept t]
  (let [f #(self-calls-without q n m kept %)]
    (cond
      (not (vector? t)) t
      (contains? #{:lit :nil :enil :bottom :cfn :dfn} (t/head t)) t
      (= :lin (t/head t)) [:lin (second t) (mapv (fn [[a k]] [(f a) k]) (nth t 2))]
      (and (= :app (t/head t)) (= q (second t)) (= (+ 2 n m) (count t)))
      (into [:app q] (concat (map f (take n (drop 2 t)))
                             (keep-indexed #(when (kept %1) (f %2)) (drop (+ 2 n) t))))
      (contains? #{:call :app} (t/head t)) (into [(first t) (second t)] (map f) (drop 2 t))
      :else (with-meta (into [(first t)] (map f) (rest t)) (meta t)))))

(defn- core-call?
  "Is ast a call of clojure.core's f with arguments matching args, each
  a node to be equal to or a predicate on the argument's node?"
  [ast f & args]
  (and (= :invoke (:op ast)) (= :ref (:op (:fn ast)))
       (= f (symbol (name (:name (:fn ast)))))
       (contains? #{nil "clojure.core"} (namespace (:name (:fn ast))))
       (= (count args) (count (:args ast)))
       (every? true? (map (fn [a x] (if (fn? a) (boolean (a x)) (= a x))) args (:args ast)))))

(defn- destructured
  "The value a map destructure takes apart: its expansion tests (seq? x),
  builds a map from x's pairs when it is one, and is x itself when it is
  not.  x's AST node, or nil.  Only that expansion matches: another test
  of seq? says something of its own."
  [ast]
  (let [t (:test ast), x (first (:args t)), th (:then ast)]
    (when (and (= :ref (:op x))
               (core-call? t 'seq? x)
               (= x (:else ast))
               (= :if (:op th))
               (core-call? (:test th) 'next x)
               (= :if (:op (:then th)))
               (core-call? (:test (:then th)) 'odd? #(core-call? % 'count x))
               (= :if (:op (:else th)))
               (core-call? (:test (:else th)) 'seq x))
      x)))

(defn- arg-term
  "An argument of a call.  A fn literal the prover cannot read -- it
  conjes onto an accumulator not known to be a vector -- is an unknown fn
  of the locals it closes over, so the call is still read: (reduce f init
  []) is init whatever f is, and a law proved for any such fn holds for
  this one.  The same literal at the same locals is the same fn."
  [ctx env a]
  (if (= :fn (:op a))
    (try (term-of ctx env a)
         (catch clojure.lang.ExceptionInfo ex
           (if (outside-reason ex)
             (let [captured (sort-by str (filter #(contains? env %) (distinct (tree-seq coll? seq (:form a)))))]
               (into [:ap (fresh ctx "u")] (map #(get env %) captured)))
             (throw ex))))
    (term-of ctx env a)))

(defn term-of
  "The term for a lowered AST node.  env maps local names to terms."
  [ctx env ast]
  (case (:op ast)
    :lit (let [v (:val ast)]
           (cond (nil? v) t/tnil
                 (and (seq? v) (empty? v)) [:sq t/enil]
                 (sequential? v) (t/value->term v)
                 (and (set? v) (every? scalar? v)) (into [:call 'hash-set] (map t/lit (t/sort-printed v)))
                 (and (map? v) (plain-data? v)) (t/value->term v)
                 (coll? v) (outside! (str "the literal " (pr-str v)))
                 :else [:lit v]))
    :ref (let [s (:name ast)]
           (cond (contains? env s) (get env s)
                 (and (not (contains? (:own ctx) s))
                      (contains? #{nil "clojure.core"} (namespace s))
                      (contains? value-fns (symbol (name s))))
                 [:cfn (symbol (name s))]
                 (contains? (:own ctx) s) [:dfn (get (:own ctx) s)]
                 (call-head ctx env s)
                 (outside! (str "`" s "` passed as a value"))
                 :else (if-let [[x] (constant ctx s)]
                         (if (set? x)
                           (into [:call 'hash-set] (map t/lit (t/sort-printed x)))
                           (t/value->term x))
                         (outside! (str "the name `" s "`")))))
    :if (if-let [x (destructured ast)]
          ;; a map destructure: on a seq it builds a map from the seq's
          ;; pairs, which the prover does not model, and anything else it
          ;; takes as it is; on a map, seq? is false and only x is left
          (let [xt (term-of ctx env x)]
            [:if [:call 'seq? xt] [:call 'writ.prove.term/map-of-seq xt] xt])
          [:if (term-of ctx env (:test ast)) (term-of ctx env (:then ast)) (term-of ctx env (:else ast))])
    ;; a statement, and a binding, is evaluated before the body, used or not:
    ;; its throws are the body's.  A binding is read where it is used, and
    ;; (strict init body) keeps that it ran
    :do (reduce (fn [body st] (strictly (term-of ctx env st) body))
                (term-of ctx env (:ret ast)) (reverse (:stmts ast)))
    :let (let [[env* inits] (reduce (fn [[e is] [b init]]
                                      (when-not (symbol? b) (outside! (str "the binding form " (pr-str b))))
                                      (let [t (term-of ctx e init)] [(assoc e b t) (conj is [b t])]))
                                    [env []] (:bindings ast))]
           ;; a binding the body reads on every path runs there anyway
           (reduce (fn [body [b i]] (if (always-read? b (:body ast)) body (strictly i body)))
                   (term-of ctx env* (:body ast)) (reverse inits)))
    :fn (do (when (:name ast) (outside! "a named local fn"))
            (let [ps (:params ast)]
              (when (or (some #(= '& %) ps) (not (every? symbol? ps)))
                (outside! "a variadic or destructuring fn"))
              (let [ps* (mapv (fn [_] (fresh ctx "p")) ps)]
                ;; a recur inside a fn literal would target the fn
                [:fn ps* (term-of (dissoc ctx :recur-target) (merge env (zipmap ps ps*)) (:body ast))])))
    :loop (let [current (or (:current ctx) (outside! "a loop outside a defn"))
                bs (:bindings ast)
                _ (when-not (every? (comp symbol? first) bs) (outside! "a destructuring loop binding"))
                ;; a loop binding's init sees the bindings before it
                [inits _] (reduce (fn [[acc e] [b init]]
                                    (let [v (term-of ctx e init)] [(conj acc v) (assoc e b v)]))
                                  [[] env] bs)
                names (mapv first bs)
                frees (vec (sort-by str (remove (set names) (keys env))))
                q (symbol (namespace current) (str (name current) "$loop" (swap! (:counter ctx) inc)))
                ps (mapv (fn [_] (fresh ctx "l")) names)
                fps (mapv (fn [_] (fresh ctx "c")) frees)
                body (term-of (assoc ctx :recur-target [q fps])
                              (merge env (zipmap frees fps) (zipmap names ps))
                              (:body ast))
                ;; the loop takes only the locals its body reads: one it
                ;; merely passes on to its own recur is left out, so a call
                ;; of the loop names only what its result depends on
                used (t/vars (self-calls-without q (count names) (count fps) #{} body))
                kept (set (keep-indexed (fn [j fp] (when (contains? used fp) j)) fps))
                body (self-calls-without q (count names) (count fps) kept body)]
            (swap! (:extra ctx) assoc q {:params (into ps (keep-indexed #(when (kept %1) %2) fps))
                                         :body body :recursive? true})
            (into [:app q] (concat inits (keep-indexed #(when (kept %1) (get env %2)) frees))))
    :recur (if-let [[q fr] (:recur-target ctx)]
             (into [:app q] (concat (map #(term-of ctx env %) (:args ast)) fr))
             (outside! "recur outside a loop"))
    :invoke (let [f (:fn ast)
                  members (when (and (= :ref (:op f)) (= 2 (count (:args ast)))
                                     (= [:core 'contains?] (call-head ctx env (:name f))))
                            (member-set ctx env (first (:args ast))))]
              (if members
                ;; membership in a set of scalars is an = against each, in
                ;; an order fixed by the values so a term is always the same
                (let [x (term-of ctx env (second (:args ast)))]
                  (reduce (fn [else m] [:if [:call '= x (t/lit m)] [:lit true] else])
                          [:lit false] (reverse (t/sort-printed members))))
                (invoke-term ctx env f (mapv #(arg-term ctx env %) (:args ast)))))

    ;; a vector literal says it is a vector, for vector?; the rest of the
    ;; prover reads it as any sequence
    :vec (with-meta (t/seq-term (mapv #(term-of ctx env %) (:items ast))) {:vector true})
    :set (into [:call 'hash-set] (map #(term-of ctx env %) (:items ast)))
    :map (into [:call 'hash-map] (mapcat (fn [k v] [(term-of ctx env k) (term-of ctx env v)])
                                         (:keys ast) (:vals ast)))
    :case (case-term ctx env ast)
    (outside! (str "`" (name (:op ast)) "`"))))

(defn lower-term
  "The term for a Clojure form, with `locals` bound to themselves; those in
  (:vector-locals ctx) are known to be vectors."
  [ctx locals form]
  (binding [l/*locals* (into (set locals) (keys (:own ctx)))]
    (term-of ctx (into {} (map (fn [x] [x (if (contains? (:vector-locals ctx) x) (with-meta x {:vector true}) x)]))
                       locals)
             (l/lower form))))

(defn- vector-params
  "The parameters of fn q its signature says are vectors."
  [ctx q params]
  (let [tys (get-in ctx [:sigs q :params])]
    (set (keep (fn [[p ty]] (when (and (seq? ty) (= 'Vec (first ty))) p))
               (map vector params tys)))))

(defn- defn-parts [f]
  (let [[_ nm & tail] f
        tail (if (string? (first tail)) (rest tail) tail)
        tail (if (map? (first tail)) (rest tail) tail)]
    {:name nm :params (first tail) :body (rest tail)}))

(defn defs-of
  "Translate every defn in `forms` (the source of namespace `ns-sym`) into
  {qualified-name {:params :body :recursive?}}, or {:outside reason} for
  one the prover cannot read.  own maps each name the forms may call
  (qualified and unqualified) to its qualified name."
  [ctx ns-sym forms]
  (merge
   (into {}
        (for [f forms
              :when (and (seq? f) (contains? '#{defn defn-} (first f)))
              :let [{:keys [name params body]} (defn-parts f)
                    ;; a destructured parameter is a plain one taken apart
                    ;; in a let, named by its position so the term is always
                    ;; the same
                    [params body] (if (and (vector? params) (not (some #{'&} params))
                                           (not-every? symbol? params))
                                    (let [ps (vec (map-indexed #(if (symbol? %2) %2 (symbol (str "p__" %1))) params))]
                                      [ps (list (list* 'let (vec (mapcat (fn [p q] (when-not (= p q) [p q])) params ps))
                                                       body))])
                                    [params body])
                    q (symbol (str ns-sym) (str name))]]
          [q (try
               (when-not (and (vector? params) (every? symbol? params) (not (some #{'&} params)))
                 (outside! (str "the parameters of `" name "`")))
               (let [b (lower-term (assoc ctx :current q :recur-target [q []] :ns ns-sym
                                          :vector-locals (vector-params ctx q params))
                                   params
                                  (if (= 1 (count body)) (first body) (cons 'do body)))]
                 {:params params :body b
                  :recursive? (boolean (some #(and (= :app (t/head %)) (= q (second %)))
                                             (t/subterms b)))})
               (catch clojure.lang.ExceptionInfo e
                 (cond
                   (outside-reason e) {:outside (outside-reason e)}
                   ;; a form writ.lower rejects, such as a destructuring fn
                   ;; literal, is outside the prover too
                   (:writ/error (ex-data e)) {:outside (str "`" name "`: " (ex-message e))}
                   :else (throw e))))]))
   ;; the loops the defns contain, each its own recursive definition
   @(:extra ctx)))

(defn own-names
  "name -> qualified name for the defns of each [ns-sym forms] pair, under
  both the plain and the qualified name."
  [pairs]
  (into {}
        (for [[ns-sym forms] pairs
              f forms
              :when (and (seq? f) (contains? '#{defn defn-} (first f)))
              :let [n (second f) q (symbol (str ns-sym) (str n))]
              k [n q]]
          [k q])))

(defn context [own] {:own own :counter (atom 0) :extra (atom {})})
