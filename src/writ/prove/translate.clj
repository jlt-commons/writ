(ns writ.prove.translate
  "Turn Clojure into prover terms.

  Definitions and law terms are lowered by writ.lower (so cond, when,
  if-let, and, or and destructuring are already let and if), then read
  into terms.  Only the fragment the rewrite rules model is accepted:
  anything else -- conj, maps, host calls, a target fn passed as a value
  -- raises `outside`, and a law that needs it is left to testing.  A
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
     sort distinct reverse last butlast take drop str name keyword})

(def value-fns
  "The clojure.core fns that may be passed as values: the modelled ones,
  and pure predicates the prover keeps opaque."
  (into core-fns '#{odd? even? nil? some? true? false?}))

(defn outside!
  "Signal a form the prover does not model."
  [what]
  (throw (ex-info (str "outside the prover: " what) {::outside what})))

(defn outside-reason [ex] (::outside (ex-data ex)))

(defn- scalar? [x]
  (or (nil? x) (number? x) (string? x) (keyword? x) (char? x) (boolean? x)))

(defn- plain-data?
  "A scalar, or a sequential of plain data, or a set of scalars."
  [x]
  (or (scalar? x)
      (and (sequential? x) (every? plain-data? x))
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

(defn- call-head
  "How a call's head is read: [:local term], [:own qualified], [:core sym]."
  [ctx env s]
  (cond
    (contains? env s) [:local (get env s)]
    (contains? (:own ctx) s) [:own (get (:own ctx) s)]
    (and (contains? #{nil "clojure.core"} (namespace s))
         (contains? core-fns (symbol (name s)))) [:core (symbol (name s))]
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
             :core (into [:call v] args)
             (outside! (str "`" (:name f) "`"))))
    :fn (into [:ap (term-of ctx env f)] args)
    (outside! "calling a computed value")))

(defn term-of
  "The term for a lowered AST node.  env maps local names to terms."
  [ctx env ast]
  (case (:op ast)
    :lit (let [v (:val ast)]
           (cond (nil? v) t/tnil
                 (and (seq? v) (empty? v)) [:sq t/enil]
                 (sequential? v) (t/value->term v)
                 (and (set? v) (every? scalar? v)) (into [:call 'hash-set] (map t/lit (sort-by pr-str v)))
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
                           (into [:call 'hash-set] (map t/lit (sort-by pr-str x)))
                           (t/value->term x))
                         (outside! (str "the name `" s "`")))))
    :if [:if (term-of ctx env (:test ast)) (term-of ctx env (:then ast)) (term-of ctx env (:else ast))]
    :do (term-of ctx env (:ret ast))
    :let (let [env* (reduce (fn [e [b init]]
                              (when-not (symbol? b) (outside! (str "the binding form " (pr-str b))))
                              (assoc e b (term-of ctx e init)))
                            env (:bindings ast))]
           (term-of ctx env* (:body ast)))
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
                              (:body ast))]
            (swap! (:extra ctx) assoc q {:params (into ps fps) :body body :recursive? true})
            (into [:app q] (concat inits (map #(get env %) frees))))
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
                          [:lit false] (reverse (sort-by pr-str members))))
                (invoke-term ctx env f (mapv #(term-of ctx env %) (:args ast)))))

    :vec (t/seq-term (mapv #(term-of ctx env %) (:items ast)))
    :set (into [:call 'hash-set] (map #(term-of ctx env %) (:items ast)))
    :case (case-term ctx env ast)
    (outside! (str "`" (name (:op ast)) "`"))))

(defn lower-term
  "The term for a Clojure form, with `locals` bound to themselves."
  [ctx locals form]
  (binding [l/*locals* (into (set locals) (keys (:own ctx)))]
    (term-of ctx (zipmap locals locals) (l/lower form))))

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
                    q (symbol (str ns-sym) (str name))]]
          [q (try
               (when-not (and (vector? params) (every? symbol? params) (not (some #{'&} params)))
                 (outside! (str "the parameters of `" name "`")))
               (let [b (lower-term (assoc ctx :current q :recur-target [q []] :ns ns-sym) params
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
