(ns writ.kind
  "Well-kindedness of the type expressions in annotations.

  A type is well-kinded when every constructor is applied to the arity it was
  declared with (writ.data), every argument is itself a type, and every name is
  a ground type, a declared type, or an in-scope name (a parameter, which in a
  dependent type may legitimately appear inside a type).")

(def base-types
  '#{Nat Bool Unit Int String Char Float Double Keyword Symbol Any})

(def builtin-ctors
  "Built-in type constructors: name -> fixed arity, or :nary for one or more.
  `List`, `Vec` and `Set` take an element type, `Map` a key and a value
  type; `Tuple` and `&` are n-ary products (the latter is a multi-value
  return).  Each is Data when its arguments are."
  {"List" 1 "Vec" 1 "Set" 1 "Map" 2 "Tuple" :nary "&" :nary})

(defn- builtin-arity [s] (get builtin-ctors (name s)))

(defn- plain [s] (symbol (name s)))
(defn- base? [s] (contains? base-types (plain s)))

(defn- fail! [& msg]
  (throw (ex-info (str "Writ: " (apply str msg)) {:writ/error true})))

(defn check-type
  "Check `ty` under `tenv` (name -> {:arity n}) with `allowed` names in scope.
  Returns true or throws."
  [ty tenv allowed]
  (cond
    (and (symbol? ty) (namespace ty) (not (contains? #{"writ.kind" "writ.core"} (namespace ty))))
    (fail! "`" ty "` is not a type; a type name is unqualified (or writ.kind/...)")

    (symbol? ty)
    (cond
      (base? ty) true
      ;; a declared type shadows a built-in constructor of the same name
      (and (contains? builtin-ctors (name ty)) (not (contains? tenv (plain ty))))
      (let [a (builtin-arity ty)]
        (fail! "`" ty "` is a type constructor; it needs "
               (if (= a :nary) "one or more" a) " type argument(s)"))
      (contains? allowed (plain ty)) true
      (contains? tenv (plain ty))
      (let [a (:arity (get tenv (plain ty)))]
        (if (zero? a)
          true
          (fail! "`" ty "` is a type constructor; it needs " a " type argument(s)")))
      :else (fail! "`" ty "` is not a type"))

    (seq? ty)
    (let [h (first ty)]
      (cond
        (and (symbol? h) (namespace h) (not (contains? #{"writ.kind" "writ.core"} (namespace h))))
        (fail! "`" h "` is not a type; a type name is unqualified (or writ.kind/...)")
        (= '-> h) (do (when (empty? (rest ty))
                        (fail! "`(->)` needs at least a result type"))
                      (doseq [a (rest ty)] (check-type a tenv allowed)) true)
        (and (symbol? h) (contains? builtin-ctors (name h))
             (not (contains? tenv (plain h))))
        (let [a (builtin-arity h) n (count (rest ty))]
          (if (or (and (= a :nary) (pos? n)) (= a n))
            (do (doseq [x (rest ty)] (check-type x tenv allowed)) true)
            (fail! "`" h "` takes " (if (= a :nary) "one or more" a) " type argument(s), got " n)))
        (symbol? h)
        (let [info (get tenv (plain h))]
          (cond
            (nil? info) (fail! "`" h "` is not a declared type")
            (not= (:arity info) (count (rest ty)))
            (fail! "`" h "` takes " (:arity info) " type argument(s), got "
                   (count (rest ty)))
            :else (do (doseq [a (rest ty)] (check-type a tenv allowed)) true)))
        :else (fail! "`" ty "` is not a type")))

    :else (fail! "`" ty "` is not a type")))

;; --- kinds ---------------------------------------------------------------

(def kind-Type :Type)
(def kind-Data :Data)

(defn function-type?
  "Is `ty` a function type `(-> A B ...)`?"
  [ty]
  (and (seq? ty) (symbol? (first ty)) (= '-> (plain (first ty)))))

(defn- subst-param
  "Substitute a declaration's type parameters into a field type."
  [ty sub]
  (cond
    (symbol? ty) (get sub (plain ty) ty)
    ;; rebuild as a list: a vector would no longer read as a type form
    (seq? ty) (with-meta (apply list (map #(subst-param % sub) ty)) (meta ty))
    :else ty))

(defn type-kind
  "Kind of a type expression, either :Data or :Type.

  A function type is :Type.  A ground type and a datatype are :Data.  A
  datatype that stores a function anywhere is :Type: directly in a field,
  through a type parameter (`(Box (-> Nat Nat))` -- a parameter carries the
  kind of what instantiates it), or nested in another datatype.  A bare type
  constructor (`Box` with its argument missing) is :Type."
  [ty tenv]
  (letfn [(k [t seen]
            (cond
              (function-type? t) kind-Type
              (symbol? t)
              (let [nm (plain t)
                    info (get tenv nm)]
                (cond
                  ;; a type variable is Data only when declared so
                  (:tvar info) (if (:data info) kind-Data kind-Type)
                  ;; only a declared ground type is provably Data; Any, a
                  ;; type parameter or a parameter used as a type is opaque
                  ;; (Bend: an opaque T: Type never licenses +)
                  (nil? info) (if (and (base? t) (not= 'Any (plain t)))
                                kind-Data
                                kind-Type)
                  (pos? (:arity info)) kind-Type
                  ;; cycle through a recursive datatype: innocent on this
                  ;; path; a fn field elsewhere is still visited separately
                  (contains? seen nm) kind-Data
                  :else (ctor-kind info (conj seen nm))))
              (seq? t)
              (let [h (first t)]
                (cond
                  (and (symbol? h) (contains? builtin-ctors (name h))
                       (not (contains? tenv (plain h))))
                  (if (some #(= kind-Type (k % seen)) (rest t)) kind-Type kind-Data)
                  (symbol? h)
                  (let [info (get tenv (plain h))]
                    (cond
                      (nil? info) kind-Type
                      (contains? seen (plain h)) kind-Data
                      :else
                      (let [args (rest t)
                            sub (zipmap (map plain (:params info)) args)]
                        (if (not= (:arity info) (count args))
                          kind-Type
                          (ctor-kind (update info :ctors
                                             (fn [cs] (into {}
                                                            (map (fn [[cn c]]
                                                                   [cn (update c :fields
                                                                               (fn [fs] (mapv #(subst-param % sub) fs)))]))
                                                            cs)))
                                     (conj seen (plain h)))))))
                  :else kind-Type))
              :else kind-Type))
        (ctor-kind [info seen]
          (if (some (fn [f] (= kind-Type (k f seen)))
                    (mapcat :fields (vals (:ctors info))))
            kind-Type
            kind-Data))]
    (k ty #{})))

(defn check-binder-kind
  "A reusable (`^:many`) binder needs a type of kind :Data.  A function type is
  never :Data, so a function-typed binder cannot be reused."
  [nm p tenv]
  (let [reusable? (= :w (:q p))
        pname (:name p)
        ty (:type p)]
    (when (and reusable? (some? ty) (not= kind-Data (type-kind ty tenv)))
      (fail! "`" pname "` in `" nm "` is reusable (^:many) but its type is not "
             "Data; a function type cannot be reused"))))
