(ns writ.defn
  "Surface macros and the helpers behind them.

  Use `(require '[writ.defn :as w])` and write ordinary Clojure:

    (w/data MaybeInt Nothing (Just Int))

    (w/defn add [a :- Nat b :- Nat] :- Nat
      (if (zero? a) b (inc (add (dec a) b))))

    (w/defn from-maybe [m :- MaybeInt]
      (w/match m :- MaybeInt
        (Nothing 0)
        ((Just x) x)))

    (w/law add-zero (forall [n Nat] (= (+ n 0) n)))
    (w/proof add-zero-refl add-zero (fn [n] refl))

  `:-` separates a name from a quantity/type annotation; a leading `:- Type`
  after the parameters is the return type.  Each macro checks its rule and
  expands to plain Clojure, so annotated code stays ordinary Clojure."
  (:refer-clojure :exclude [defn])
  (:require [writ.check :as ck]
            [writ.ann :as ann]
            [writ.data :as dt]
            [writ.kind :as kind]
            [writ.match :as mt]))

(def sig-registry
  "ns name -> fn name -> {:params [type] :ret type}: the signatures of the
  w/defns expanded so far, so a later w/defn's calls are type-checked at
  expansion time the way check-book checks them."
  (atom {}))

(clojure.core/defn- plain-sym [s] (symbol (clojure.core/name s)))

(clojure.core/defn- plain-type [t]
  (cond
    (symbol? t) (plain-sym t)
    (seq? t) (apply list (map plain-type t))
    :else t))

(clojure.core/defn- split-annotated [params]
  (loop [toks (seq params), out []]
    (if (empty? toks)
      out
      (let [nm (first toks), nxt (second toks)]
        (if (= ':- nxt)
          (if-not (nthnext toks 2)
            (throw (ex-info "Writ: `:-` must be followed by a type"
                            {:writ/error true}))
            (recur (drop 3 toks) (conj out [nm (nth toks 2)])))
          (recur (rest toks) (conj out [nm nil])))))))

(clojure.core/defn- quantity-ann [a]
  (cond
    (contains? #{:omega :reusable :many :w} a) :w
    (contains? #{:affine :once :1} a)          :1
    (contains? #{:zero :erased :0} a)          :0
    :else nil))

(clojure.core/defn- annotate [nm a]
  (cond
    (quantity-ann a) (vary-meta nm assoc :writ/q (quantity-ann a))
    (some? a) (vary-meta nm assoc :tag a)
    :else nm))

(clojure.core/defn- fn-head? [f]
  (and (seq? f) (symbol? (first f)) (contains? #{"fn" "fn*"} (clojure.core/name (first f)))))

(clojure.core/defn annotate-fns
  "Rewrite every `(fn name? [x :- T ...] body)` in `form` to carry its
  annotations as binder metadata, `(fn name? [^{:writ/type T} x ...] body)`:
  the plain form Clojure compiles, with the types where the checker reads
  them."
  [form]
  (cond
    (and (fn-head? form)
         (let [tail (rest form)
               ps (if (symbol? (first tail)) (second tail) (first tail))]
           (and (vector? ps) (some #{:-} ps))))
    (let [tail (rest form)
          named? (symbol? (first tail))
          ps (if named? (second tail) (first tail))
          body (if named? (drop 2 tail) (rest tail))
          ps* (mapv (fn [[s a]]
                      (cond
                        (quantity-ann a) (vary-meta s assoc :writ/q (quantity-ann a))
                        (some? a) (vary-meta s assoc :writ/type a)
                        :else s))
                    (split-annotated ps))]
      (apply list (first form)
             (concat (when named? [(first tail)]) [ps*] (map annotate-fns body))))

    (seq? form) (with-meta (apply list (map annotate-fns form)) (meta form))
    (vector? form) (with-meta (mapv annotate-fns form) (meta form))
    (map? form) (into (empty form) (map (fn [[k v]] [(annotate-fns k) (annotate-fns v)])) form)
    :else form))

(clojure.core/defn forall-tenv
  "`tenv` extended with the type variables a defn declares in its
  attr-map, {:writ/forall [a, b :- Data]}: erased by construction (no
  runtime argument), kind Type unless declared Data."
  [nm tenv]
  (let [vs (:writ/forall (meta nm))]
    (when (and (some? vs) (not (vector? vs)))
      (throw (ex-info (str "Writ: `:writ/forall` in `" nm "` takes a vector of type variables")
                      {:writ/error true})))
    (reduce (fn [t [v k]]
              (when-not (and (symbol? v) (nil? (namespace v)))
                (throw (ex-info (str "Writ: a type variable in `" nm "` must be a simple symbol: `" v "`")
                                {:writ/error true})))
              (when-not (contains? #{nil 'Type 'Data} (some-> k plain-sym))
                (throw (ex-info (str "Writ: type variable `" v "` in `" nm "` has kind Type or Data, not `" k "`")
                                {:writ/error true})))
              (assoc t v {:arity 0 :params [] :ctors {} :tvar true
                          :data (= 'Data (some-> k plain-sym))}))
            tenv
            (split-annotated vs))))

(clojure.core/defn build
  "The plain `defn` form a `w/defn` expands to."
  [nm params body]
  (let [pairs (split-annotated params)
        psyms (mapv (fn [[s a]] (annotate s a)) pairs)
        [ret body*] (if (= ':- (first body))
                      [(second body) (rest (rest body))]
                      [nil body])
        nm* (if ret (vary-meta nm assoc :tag ret) nm)]
    (with-meta (concat (list 'clojure.core/defn nm* psyms) body*)
      {:writ/ret ret})))

(clojure.core/defn signature
  "Read a plain defn form (params carry metadata) into
  {:name :params [{:name :q :type}] :ret}."
  [form]
  (let [[_ nm & tail] form
        tail (if (string? (first tail)) (rest tail) tail)
        tail (if (map? (first tail)) (rest tail) tail)
        _ (when-not (or (vector? (first tail))
                        (nil? (first tail))
                        (and (sequential? (first tail)) (seq (first tail))
                             (vector? (first (first tail)))))
            (throw (ex-info (str "Writ: `" nm "` requires a vector of parameters")
                            {:writ/error true})))
        params (vec (first tail))
        _ (when (some (complement symbol?) params)
            (throw (ex-info (str "Writ: `" nm "` is multi-arity; writ checks a single arity")
                            {:writ/error true})))]
    {:name nm
     :ret (:tag (meta nm))
     :params (mapv (fn [p] {:name p :q (ann/quantity-of p)
                            :type (or (:writ/type (meta p)) (:tag (meta p)))})
                   params)}))

(clojure.core/defn check
  "Check a `w/defn` signature and body without expanding.  Returns {:ok true}."
  [nm params body]
  (when-not (vector? params)
    (throw (ex-info (if (and (sequential? params) (seq params)
                          (vector? (first params)))
                      (str "Writ: `" nm "` is multi-arity; writ checks a single arity")
                      (str "Writ: `" nm "` requires a vector of parameters"))
                    {:writ/error true})))
  (when (and (= ':- (first body)) (nil? (second body)))
    (throw (ex-info (str "Writ: `:-` in `" nm "` must be followed by a return type")
                    {:writ/error true})))
  (let [form (build nm params body)
        sig (signature form)
        tenv (forall-tenv nm @dt/registry)
        allowed (set (map (fn [p] (symbol (clojure.core/name (:name p)))) (:params sig)))]
    (doseq [[i p] (map-indexed vector (:params sig))]
      (when (:type p)
        (kind/check-type (:type p) tenv
                         (set (map (fn [q] (symbol (clojure.core/name (:name q))))
                                   (take i (:params sig))))))
      (kind/check-binder-kind (:name sig) p tenv))
    (when (:ret sig) (kind/check-type (:ret sig) tenv allowed))
    (ck/check-defn form nil nil nil
                   {:tenv tenv
                    :sigs (get @sig-registry (ns-name *ns*))})
    (swap! sig-registry assoc-in [(ns-name *ns*) (plain-sym (:name sig))]
           {:params (mapv (fn [p] (some-> (:type p) plain-type))
                          (remove #(= '& (:name %)) (:params sig)))
            :ret (some-> (:ret sig) plain-type)})
    {:ok true}))

(clojure.core/defmacro defn [nm & tail]
  ;; the attr-map position is defn metadata, as in clojure.core/defn
  (let [[nm params body] (if (map? (first tail))
                           [(vary-meta nm merge (first tail)) (second tail) (drop 2 tail)]
                           [nm (first tail) (rest tail)])
        ps (into {} (comp (map first) (filter symbol?)
                          (map (fn [s] [(symbol (clojure.core/name s))
                                        (ann/quantity-of s)])))
                  (split-annotated params))
        types (into {} (keep (fn [[s t]] (when (and (symbol? s) t (not (quantity-ann t)))
                                           [(symbol (clojure.core/name s)) (plain-type t)])))
                    (split-annotated params))
        body (mapv (fn [b] (mt/rewrite (forall-tenv nm @dt/registry) ps (annotate-fns b) types)) body)]
    (check nm params body)
    (build nm params body)))

(clojure.core/defmacro data [& args]
  (let [info (dt/parse (cons 'writ.data args))
        env (dt/env info)]
    ;; registered now, for a `match` later in this file to expand against,
    ;; and again when the code runs, because a namespace loaded from a
    ;; compiled cache is never macroexpanded
    (swap! dt/registry assoc (:name info) env)
    (list 'do
          (list 'clojure.core/swap! 'writ.data/registry 'clojure.core/assoc
                (list 'quote (:name info)) (list 'quote env))
          (list 'clojure.core/def (:name info) (list 'quote info)))))

(clojure.core/defmacro law [nm prop]
  (list 'clojure.core/def nm (list 'quote prop)))

(clojure.core/defmacro proof [nm law-name body]
  (list 'clojure.core/def nm (list 'quote body)))

(clojure.core/defmacro match [& args]
  (mt/rewrite @dt/registry {} (list* 'writ.match/match args)))
