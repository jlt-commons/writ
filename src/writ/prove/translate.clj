(ns writ.prove.translate
  "Turn Clojure into prover terms.

  Definitions and law terms are lowered by writ.lower (so cond, when,
  if-let, and, or and destructuring are already let and if), then read
  into terms.  Only the fragment the rewrite rules model is accepted:
  anything else -- conj, maps, loop/recur, host calls, a fn passed as a
  value -- raises `outside`, and a law that needs it is left to testing."
  (:require [writ.lower :as l]
            [writ.prove.term :as t]))

(def core-fns
  "The clojure.core fns the prover models."
  '#{seq first rest next second empty? count cons list vector vec concat
     filter map not = < <= > >= + - * inc dec zero? pos? neg? nth identity})

(defn outside!
  "Signal a form the prover does not model."
  [what]
  (throw (ex-info (str "outside the prover: " what) {::outside what})))

(defn outside-reason [ex] (::outside (ex-data ex)))

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

(defn term-of
  "The term for a lowered AST node.  env maps local names to terms."
  [ctx env ast]
  (case (:op ast)
    :lit (let [v (:val ast)]
           (cond (nil? v) t/tnil
                 (and (seq? v) (empty? v)) [:sq t/enil]
                 (sequential? v) (t/value->term v)
                 (coll? v) (outside! (str "the literal " (pr-str v)))
                 :else [:lit v]))
    :ref (let [s (:name ast)]
           (cond (contains? env s) (get env s)
                 (or (contains? (:own ctx) s) (call-head ctx env s))
                 (outside! (str "`" s "` passed as a value"))
                 :else (outside! (str "the name `" s "`"))))
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
                [:fn ps* (term-of ctx (merge env (zipmap ps ps*)) (:body ast))])))
    :invoke (let [f (:fn ast)
                  args (mapv #(term-of ctx env %) (:args ast))]
              (case (:op f)
                :ref (let [[k v] (call-head ctx env (:name f))]
                       (case k
                         :local (into [:ap v] args)
                         :own (into [:app v] args)
                         :core (into [:call v] args)
                         (outside! (str "`" (:name f) "`"))))
                :fn (into [:ap (term-of ctx env f)] args)
                (outside! "calling a computed value")))
    :vec (t/seq-term (mapv #(term-of ctx env %) (:items ast)))
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
  (into {}
        (for [f forms
              :when (and (seq? f) (contains? '#{defn defn-} (first f)))
              :let [{:keys [name params body]} (defn-parts f)
                    q (symbol (str ns-sym) (str name))]]
          [q (try
               (when-not (and (vector? params) (every? symbol? params) (not (some #{'&} params)))
                 (outside! (str "the parameters of `" name "`")))
               (let [b (lower-term ctx params (if (= 1 (count body)) (first body) (cons 'do body)))]
                 {:params params :body b
                  :recursive? (boolean (some #(and (= :app (t/head %)) (= q (second %)))
                                             (t/subterms b)))})
               (catch clojure.lang.ExceptionInfo e
                 (cond
                   (outside-reason e) {:outside (outside-reason e)}
                   ;; a form writ.lower rejects, such as a destructuring fn
                   ;; literal, is outside the prover too
                   (:writ/error (ex-data e)) {:outside (str "`" name "`: " (ex-message e))}
                   :else (throw e))))])))

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

(defn context [own] {:own own :counter (atom 0)})
