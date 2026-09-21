(ns writ.data
  "Data type declarations, in the shape

    (w/data Maybe [a]
      Nothing
      (Just a))

  `Maybe` is a type constructor of arity 1 (one type parameter, `a`).
  `Nothing` has no fields; `Just` has one field of type `a`.  `parse` reads the
  declaration; `registry` holds what a namespace has declared so the `w/match`
  macro can check its patterns.")

(def registry (atom {}))

(defn- params-and-ctors [form]
  (let [tail (drop 2 form)]
    (if (vector? (first tail))
      [(vec (first tail)) (rest tail)]
      [[] tail])))

(defn- bad-shape!
  [& msg]
  (throw (ex-info (str "Writ: " (apply str msg)) {:writ/error true})))

(defn- simple-sym? [x] (and (symbol? x) (nil? (namespace x))))

(defn parse
  "Parse (data Name [params...] ctor...).  Returns
  {:name N :params [syms] :ctors {Ctor {:fields [type-forms]}}}.
  The head shape is validated here: a book is never compiled, so no host
  contract catches a malformed declaration."
  [form]
  (let [nm (second form)
        _ (if (nil? nm)
            (bad-shape! "`data` requires a name")
            (when-not (simple-sym? nm)
              (bad-shape! "a `data` name must be a simple symbol: `" nm "`")))
        [params ctors] (params-and-ctors form)
        _ (doseq [p params]
            (when-not (and (symbol? p) (nil? (namespace p))
                           (not (re-find #"\." (name p))))
              (bad-shape! "a type parameter in `" nm "` must be a simple "
                          "symbol: `" p "`")))
        _ (when-let [dup (some (fn [p] (when (< 1 (count (filter #{p} params))) p))
                                params)]
            (bad-shape! "duplicate type parameter in `" nm "`: `" dup
                        "` appears twice"))
        _ (let [names (map (fn [c] (if (seq? c) (first c) c)) ctors)]
            (when-let [dup (first (filter #(< 1 (count (filter #{%} names))) names))]
              (bad-shape! "constructor `" dup "` is declared twice in `" nm "`")))
        ctors (reduce (fn [m c]
                        (cond
                          (simple-sym? c) (assoc m c {:fields []})
                          (seq? c) (let [cname (first c)]
                                     (when-not (simple-sym? cname)
                                       (bad-shape! "a constructor name must be a "
                                                   "simple symbol: `" cname "`"))
                                     (assoc m cname {:fields (vec (rest c))}))
                          :else (bad-shape! "a constructor must be a symbol or a "
                                            "`(name fields*)` form: `" c "`")))
                      {} ctors)]
    {:name nm :params params :ctors ctors}))

(defn env
  "The type-environment entry for a declaration: arity, type params and
  constructors (params included so kind substitution can instantiate them)."
  [decl]
  {:arity (count (:params decl)) :params (:params decl) :ctors (:ctors decl)})

(defn data-form?
  [form]
  (and (seq? form) (symbol? (first form)) (= "data" (name (first form)))))
