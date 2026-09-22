(ns writ.types
  "A minimal type checker over the lowered AST.

  Types come from annotations (`:- T` in w/defn, which expands to a :tag,
  or ^T / ^{:writ/type T} on a plain defn) and from a small inference:
  literals, the core arithmetic, predicate and collection fns, book fn
  signatures and pattern binders (a match hands each binder its field
  type).  Anything else is unknown, and an unknown type never fails a
  check -- except where Bend demands a proof: `+x = v` needs v's type to
  be Data, so a reusable binder must carry or infer one.

  Checked: reusable binders are Data, call arguments against the callee's
  parameter types, the body against the declared return type, and a
  value in call position must be a function."
  (:require [writ.kind :as kind]
            [writ.ann :as ann]
            [writ.lower :as l]))

(defn- fail! [& msg]
  (throw (ex-info (str "Writ: " (apply str msg)) {:writ/error true})))

(def data
  "An inferred type known to be Data but otherwise unspecified (a
  collection of Data, a quoted form)."
  :writ/data)

(def infinite
  "An inferred lazy seq with no end: (range), (repeat x), (iterate f x),
  (cycle xs), (repeatedly f), and lazy transforms of one.  Data, but never
  a finite collection."
  :writ/infinite)

(defn- finite-coll? [t tenv]
  (and (some? t)
       (or (= 'String t)
           (and (seq? t) (contains? '#{List Vec Set Map} (first t)))
           (and (symbol? t) (contains? tenv t) (not (:tvar (get tenv t))))
           (and (seq? t) (contains? tenv (first t))))))

(defn plain-type
  "A type with namespaces dropped from its names: writ.kind/Nat is Nat."
  [t]
  (cond
    (symbol? t) (symbol (name t))
    (seq? t) (apply list (map plain-type t))
    :else t))

(defn- known?
  "Is `t` a type writ understands, rather than a host class hint?"
  [t tenv]
  (cond
    (= data t) true
    (symbol? t) (or (contains? kind/base-types t) (contains? tenv t))
    (seq? t) (let [h (first t)]
               (and (symbol? h)
                    (or (= '-> h) (contains? kind/builtin-ctors (name h))
                        (contains? tenv h))))
    :else false))

(defn binder-type
  "The type a binder is annotated with, or nil."
  [b tenv]
  (when (symbol? b)
    (let [m (meta b)
          t (some-> (or (:writ/type m) (:tag m)) plain-type)]
      (when (and t (known? t tenv)) t))))

(defn- data? [t tenv]
  (or (= data t) (= infinite t) (and (some? t) (= kind/kind-Data (kind/type-kind t tenv)))))

(defn- show [t]
  (cond (= data t) "data"
        (= infinite t) "an infinite seq"
        :else (pr-str t)))

(defn compat?
  "May a value of type `act` stand where `exp` is expected?  Unknowns
  pass; Nat widens to Int and any integer to a float."
  [exp act tenv]
  (cond
    (or (nil? exp) (nil? act)) true
    ;; a lazy seq with no end is not a finite collection
    (= infinite act) (not (finite-coll? exp tenv))
    ;; a type variable stands for any type
    (or (:tvar (get tenv exp)) (:tvar (get tenv act))) true
    (or (= data exp) (= data act)) true
    (= exp act) true
    (not (known? exp tenv)) true
    (= 'Any exp) true
    (and (= 'Int exp) (= 'Nat act)) true
    ;; a String is a finite seq of chars
    (and (= '(List Char) exp) (= 'String act)) true
    (and (contains? '#{Float Double} exp) (contains? '#{Nat Int Float Double} act)) true
    (and (kind/function-type? exp) (kind/function-type? act)) true
    (and (seq? exp) (seq? act) (= (first exp) (first act))
         (= (count exp) (count act)))
    (every? true? (map #(compat? %1 %2 tenv) (rest exp) (rest act)))
    :else false))

(defn- join [a b tenv]
  (cond
    (= a b) a
    (and (contains? '#{Nat Int} a) (contains? '#{Nat Int} b)) 'Int
    (and (data? a tenv) (data? b tenv)) data
    :else nil))

;; --- core fns ------------------------------------------------------------

(def ^:private numeric-nat
  "Arithmetic that stays in Nat when every argument is Nat."
  '#{inc + * quot rem mod max min})

(def ^:private numeric
  (into numeric-nat '#{dec - abs}))

(def ^:private predicates
  '#{zero? pos? neg? even? odd? = not= < > <= >= == not empty? nil? some?
     contains? true? false? number? integer? int? nat-int? pos-int? neg-int?
     string? keyword? symbol? map? vector? set? seq? coll? fn? boolean?
     identical? every? not-every? not-any? distinct? sequential?})

(def ^:private collection-builders
  '#{vector list hash-map hash-set array-map sorted-map conj assoc dissoc
     disj cons concat into merge vec set reverse sort take drop keys vals
     butlast subvec distinct list*})

(def ^:private element-readers '#{first second last peek nth get})

(def ^:private lazy-transforms
  "Core fns whose result is infinite when a collection argument is."
  '#{map mapcat filter remove keep map-indexed keep-indexed rest next drop
     drop-while take-while take-nth seq concat interleave distinct dedupe
     partition partition-all reductions})

(defn- core-ret [f args tenv]
  (cond
    (or (and (= 'range f) (empty? args))
        (and (= 'repeat f) (= 1 (count args)))
        (and (= 'repeatedly f) (= 1 (count args)))
        (contains? '#{iterate cycle} f))
    infinite
    (and (contains? lazy-transforms f) (some #(= infinite %) args))
    infinite
    (and (= 'take f) (some #(= infinite %) args))
    data
    (contains? numeric f)
    (cond
      (some #(contains? '#{Float Double} %) args) 'Double
      (and (contains? numeric-nat f) (seq args) (every? #(= 'Nat %) args)) 'Nat
      (every? #(contains? '#{Nat Int} %) args) 'Int
      ;; a number either way (or a throw): Data, width unknown
      :else data)
    (contains? predicates f) 'Bool
    (= 'count f) 'Nat
    (contains? '#{str subs pr-str} f) 'String
    (= 'keyword f) 'Keyword
    (= 'range f) data
    (contains? collection-builders f)
    (when (every? #(data? % tenv) args) data)
    (contains? '#{seq rest next} f)
    (let [c (first args)]
      (cond
        (and (seq? c) (contains? '#{List Vec} (first c))) (list 'List (second c))
        (= 'String c) '(List Char)
        :else
        (when (every? #(data? % tenv) args) data)))
    (contains? element-readers f)
    (let [c (first args)]
      (when (and (seq? c) (= 'List (first c))) (second c)))
    :else nil))

;; --- the walk ------------------------------------------------------------

(defn- temp? [b]
  (or (:writ/temp (meta b))
      (and (symbol? b) (re-find #"(?:^G__\d+|__auto)(?:__\d+)?$" (name b)))))

(defn- display [s]
  (if (symbol? s) (symbol (clojure.string/replace (name s) #"__\d+$" "")) s))

(defn lit-type [v]
  (cond
    (integer? v) (if (neg? v) 'Int 'Nat)
    (or (double? v) (float? v)) 'Double
    (string? v) 'String
    (char? v) 'Char
    (boolean? v) 'Bool
    (keyword? v) 'Keyword
    (symbol? v) 'Symbol
    (nil? v) 'Unit
    (coll? v) data
    :else nil))

(def ^:private seq-readers
  "Core fns that read a value's runtime encoding by position."
  '#{first second last nth nthnext nthrest rest next seq peek get ffirst
     fnext nnext subvec count})

(def ^:private not-callable '#{Nat Int Bool String Char Float Double Unit})

(defn- check-reusable! [nm b t tenv]
  (when (and (= :w (ann/quantity-of b)) (not (temp? b)))
    (cond
      (nil? t)
      (fail! "`" (display b) "` in `" nm "` is reusable (^:many) but its value has "
             "no type writ can infer; annotate it with a Data type (^Nat, or "
             "`:- Nat` in w/defn)")
      (not (data? t tenv))
      (fail! "`" (display b) "` in `" nm "` is reusable (^:many) but its type "
             (show t) " is not Data; a function type cannot be reused"))))

(defn- guard-refs
  "Names a test proves nonzero: [then-branch else-branch].  (zero? x) and
  (= x 0) prove x nonzero in the else branch; (pos? x), (< 0 x) and
  (> x 0) in the then branch; `not` swaps them."
  [test]
  (let [ref-name (fn [a] (when (and (map? a) (= :ref (:op a))) (:name a)))
        zero-lit? (fn [a] (and (map? a) (= :lit (:op a)) (= 0 (:val a))))
        head (when (and (= :invoke (:op test)) (= :ref (:op (:fn test))))
               (symbol (name (:name (:fn test)))))
        [a b] (:args test)]
    (case head
      zero? (if-let [x (ref-name a)] [#{} #{x}] [#{} #{}])
      pos? (if-let [x (ref-name a)] [#{x} #{}] [#{} #{}])
      = (cond (and (ref-name a) (zero-lit? b)) [#{} #{(ref-name a)}]
              (and (zero-lit? a) (ref-name b)) [#{} #{(ref-name b)}]
              :else [#{} #{}])
      < (if (and (zero-lit? a) (ref-name b)) [#{(ref-name b)} #{}] [#{} #{}])
      > (if (and (ref-name a) (zero-lit? b)) [#{(ref-name a)} #{}] [#{} #{}])
      not (let [[t e] (guard-refs a)] [e t])
      [#{} #{}])))

(defn- walk [ctx env ast]
  (let [{:keys [nm tenv sigs]} ctx
        w (fn [e a] (walk ctx e a))]
    (case (:op ast)
      :lit (lit-type (:val ast))
      :ref (or (get env (:name ast))
               (when-let [s (and (not (contains? env (:name ast)))
                                 (get sigs (:name ast)))]
                 (apply list '-> (concat (map #(or % 'Any) (:params s))
                                         [(or (:ret s) 'Any)]))))
      (:vec :set) (let [ts (mapv #(w env %) (:items ast))]
                    (when (every? #(data? % tenv) ts) data))
      :map (let [ts (mapv #(w env %) (concat (:keys ast) (:vals ast)))]
             (when (every? #(data? % tenv) ts) data))
      :do (do (doseq [s (:stmts ast)] (w env s)) (w env (:ret ast)))
      :if (let [[pt pe] (guard-refs (:test ast))
                pos (fn [e xs] (update e ::pos (fnil into #{}) xs))]
            (w env (:test ast))
            (join (w (pos env pt) (:then ast)) (w (pos env pe) (:else ast)) tenv))
      :case (do (w env (:scrut ast))
                (reduce (fn [acc b] (join acc (w env b) tenv))
                        (map #(w env (:body %)) (cond-> (vec (:clauses ast))
                                                  (:default ast) (conj {:body (:default ast)})))))
      (:let :loop)
      (let [env* (reduce (fn [e [b init]]
                           (let [it (w e init)
                                 bt (binder-type b tenv)]
                             (when (and bt it (not (compat? bt it tenv)))
                               (fail! "`" (display b) "` in `" nm "` is declared "
                                      (show bt) " but bound to " (show it)))
                             (let [t (or bt it)]
                               (check-reusable! nm b t tenv)
                               (cond-> (assoc e b t)
                                 (:writ/temp (meta b)) (update ::temps (fnil conj #{}) b)))))
                         env (:bindings ast))]
        (w env* (:body ast)))
      :fn (let [ps (remove nil? (:params ast))
                env* (into (cond-> env (:name ast) (assoc (:name ast) nil))
                           (map (fn [p] [p (binder-type p tenv)])) ps)
                _ (doseq [p ps]
                    (when-let [t (:writ/type (meta p))]
                      (kind/check-type t tenv #{}))
                    (check-reusable! nm p (binder-type p tenv) tenv))
                rt (w env* (:body ast))]
            (apply list '-> (concat (map #(or (binder-type % tenv) 'Any) ps)
                                    [(or rt 'Any)])))
      :recur (do (doseq [a (:args ast)] (w env a)) nil)
      :invoke
      (let [f (:fn ast)
            ats (mapv #(w env %) (:args ast))]
        (if-not (and (map? f) (= :ref (:op f)))
          (do (w env f) nil)
          (let [s (:name f)
                local? (contains? env s)
                lt (get env s)]
            (cond
              (and local? lt (or (contains? not-callable lt)
                                 (and (contains? tenv lt) (not (:tvar (get tenv lt))))
                                 (and (seq? lt) (contains? tenv (first lt)))))
              (fail! "`" (display s) "` has type " (show lt) ", which is not a "
                     "function; it cannot be applied")

              local? (when (kind/function-type? lt) (last lt))

              ;; under a guard proving it nonzero, dec of a Nat stays Nat
              ;; (Bend's 1n+p arm)
              (and (= 'dec (symbol (name s))) (not (contains? (:shadow ctx) s))
                   (= 1 (count (:args ast))) (= :ref (:op (first (:args ast))))
                   (= 'Nat (first ats))
                   (contains? (::pos env) (:name (first (:args ast)))))
              'Nat

              (get sigs s)
              (let [{:keys [params ret]} (get sigs s)]
                (doseq [[i pt at] (map vector (range) params ats)]
                  (when-not (compat? pt at tenv)
                    (fail! "`" (display s) "` expects " (show pt) " for argument "
                           (inc i) " but is passed " (show at))))
                ret)

              (and (contains? seq-readers (symbol (name s)))
                   (or (nil? (namespace s)) (= "clojure.core" (namespace s)))
                   (not (contains? (:shadow ctx) s))
                   (let [a (first (:args ast)) t (first ats)]
                     (and (map? a) (= :ref (:op a))
                          (not (contains? (::temps env) (:name a)))
                          (or (and (contains? tenv t) (not (:tvar (get tenv t))))
                              (and (seq? t) (contains? tenv (first t)))))))
              (fail! "`" (display (:name (first (:args ast)))) "` has data type "
                     (show (first ats)) "; take it apart with `match`, not `"
                     (symbol (name s)) "` (its encoding is not its interface)")

              (and (nil? (namespace s)) (not (contains? (:shadow ctx) s)))
              (core-ret s ats tenv)

              (= "clojure.core" (namespace s))
              (core-ret (symbol (name s)) ats tenv)

              :else nil))))
      nil)))

(defn check-types
  "Run the type checks over a uniquified defn body.  `ctx` carries :tenv
  (declared datatypes), :sigs (book fn name -> {:params [type] :ret type})
  and :shadow (the book's names)."
  [nm params ret body-ast ctx]
  (let [tenv (or (:tenv ctx) {})
        ctx (assoc ctx :nm nm :tenv tenv)
        ps (filter symbol? params)
        env (into {} (map (fn [p] [p (binder-type p tenv)])) ps)]
    (doseq [p ps]
      (when-let [t (:writ/type (meta p))]
        (kind/check-type t tenv #{}))
      (when (and (= :w (ann/quantity-of p)) (nil? (get env p)))
        (fail! "`" p "` in `" nm "` is reusable (^:many) but has no type; "
               "annotate it with a Data type (^Nat on a plain defn, `:- Nat` "
               "in w/defn)"))
      (check-reusable! nm p (get env p) tenv))
    (let [rt (walk ctx env body-ast)
          ret (some-> ret plain-type)]
      (when (and ret (known? ret tenv) (not (compat? ret rt tenv)))
        (fail! "`" nm "` returns " (show ret) " but its body has type " (show rt))))))
