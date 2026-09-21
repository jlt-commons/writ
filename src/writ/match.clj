(ns writ.match
  "Match discipline.

  A match inspects a parameter or a value bound by an earlier pattern, never a
  computed expression (bend's guide: `match sum(xs, 0)` is rejected), so the
  scrutinee is checked against the scope of names the enclosing defn binds;
  a let, loop or destructure that rebinds a name takes it out of scope.
  When the scrutinee's type is known it must be the match type.

  An arm is `((Ctor binder ...) body)`, `(Ctor body)` for a fieldless
  constructor, or a catch-all `(name body)` last, which binds the rest of
  the value.  Every constructor is covered exactly once; a type with no
  constructors is matched with no arms.  A pattern binder is a plain
  symbol (`_` may repeat): nest a second match to look deeper.

  Pattern binders carry quantities like any binder: an unmarked binder
  takes its field's quantity (`(data P (MkP ^:many Nat))`), `(Node ^:many v
  l r)` reuses `v`, and when the scrutinee is reusable BendTT 2.3 hands
  every non-erased field out reusable too.  The match type may be a
  declared name or a parametric application `(Box Nat)`."
  (:require [writ.kind :as kind]
            [writ.ann :as ann]
            [writ.lower :as l]
            [writ.types :as ty]))

(defn- fail! [& msg]
  (throw (ex-info (str "Writ: " (apply str msg)) {:writ/error true})))

(defn- plain [s] (symbol (name s)))

(defn- subst
  "Substitute a declaration's type parameters into a field type."
  [ty sub]
  (cond
    (symbol? ty) (get sub (plain ty) ty)
    (seq? ty) (with-meta (apply list (map #(subst % sub) ty)) (meta ty))
    :else ty))

(defn- head-name [form]
  (let [h (first form)]
    (when (symbol? h) (name h))))

(defn- parse-arm
  "{:ctor c :binders [..] :body b} for a constructor arm, {:catch name
  :body b} for a bare name that is not a constructor of the type."
  [af ctors]
  (when-not (and (seq? af) (= 2 (count af)))
    (fail! "a match arm must be `(pattern result)`, had: `" (pr-str af) "`"))
  (let [[pat body] af]
    (cond
      (symbol? pat)
      (cond
        (namespace pat)
        (fail! "`" pat "` is a qualified name; a pattern names a constructor of "
               "the match type unqualified")
        (contains? ctors pat) {:ctor pat :binders [] :body body}
        ;; a capitalised name reads as a constructor (a typo is not a
        ;; catch-all); a lowercase name or _ binds the rest, as in Bend
        (Character/isUpperCase (char (first (name pat))))
        {:ctor pat :binders [] :body body}
        :else {:catch pat :body body})

      (seq? pat)
      (let [c (first pat)]
        (when-not (and (symbol? c) (nil? (namespace c)))
          (fail! "`" (pr-str c) "` in `" (pr-str pat) "` is not a constructor name; a "
                 "pattern is `(Ctor binder ...)`"))
        (doseq [b (rest pat)]
          (when-not (and (symbol? b) (l/valid-binding-symbol? b))
            (fail! "a pattern binder must be a symbol, had `" (pr-str b) "` in `"
                   (pr-str pat) "`; match the field again to look inside it")))
        {:ctor c :binders (vec (rest pat)) :body body})

      :else
      (fail! "a match pattern must be a constructor, `(Ctor binder ...)` or a "
             "catch-all name, had `" (pr-str pat) "`"))))

(defn- resolve-type
  "Resolve the match type: a declared name, or a parametric application.
  Returns {:name :entry}."
  [tenv scope ty]
  (cond
    (symbol? ty)
    (let [entry (get tenv (symbol (name ty)))]
      (when (nil? entry)
        (fail! "`" ty "` is not a declared data type"))
      (when (pos? (:arity entry))
        (fail! "`" ty "` is a type constructor; it needs " (:arity entry)
               " type argument(s)"))
      {:name ty :entry entry})

    (seq? ty)
    (let [h (first ty)]
      (when-not (symbol? h)
        (fail! "the match type must be a named type"))
      (let [entry (get tenv (symbol (name h)))]
        (when (nil? entry)
          (fail! "`" h "` is not a declared data type"))
        (when (not= (:arity entry) (count (rest ty)))
          (fail! "`" h "` takes " (:arity entry) " type argument(s), got "
                 (count (rest ty))))
        (doseq [a (rest ty)] (kind/check-type a tenv scope))
        {:name h :entry entry}))

    :else (fail! "the match type must be a named type")))

(defn- check-arms! [ty ctors arms]
  (doseq [[i arm] (map-indexed vector arms)]
    (if (:catch arm)
      (when (< i (dec (count arms)))
        (fail! "a catch-all arm `" (:catch arm) "` in a match on `" ty "` must be "
               "last; the arms after it can never run"))
      (let [ctor (:ctor arm)
            binders (:binders arm)
            info (get ctors (symbol (name ctor)))]
        (when (nil? info)
          (fail! "`" ctor "` is not a constructor of `" ty "`"))
        (when (not= (count (:fields info)) (count binders))
          (fail! "`" ctor "` takes " (count (:fields info))
                 " field(s); the pattern binds " (count binders)))
        (let [named (remove #{'_} binders)]
          (when (not= (count named) (count (distinct named)))
            (fail! "duplicate binder in a pattern for `" ctor "`"))))))
  (let [have (mapv (fn [a] (symbol (name (:ctor a)))) (remove :catch arms))]
    (when (not= (count have) (count (distinct have)))
      (fail! "a match on `" ty "` repeats a constructor"))
    (let [missing (remove (set have) (keys ctors))]
      (when (and (seq missing) (not (some :catch arms)))
        (fail! "a match on `" ty "` is not exhaustive; missing "
               (apply str (interpose ", " (map str missing))))))))

(defn- many [s] (vary-meta s assoc :writ/q :w))

(defn- explicit-q
  "The quantity a symbol's metadata states, or nil when it states none."
  [s]
  (let [m (meta s)]
    (when (some #(contains? m %) [:writ/q :q :many :reusable :omega :zero :erased
                                  :once :affine])
      (ann/quantity-of s))))

(defn- effective-qty
  "The quantity a pattern binder carries: its own annotation, else its
  field's declared quantity, else affine; and when the scrutinee is
  reusable, the field times the scrutinee (BendTT 2.3) -- only an erased
  field stays erased."
  [b field scr-q]
  (let [q (or (explicit-q b) (when (symbol? field) (explicit-q field)) :1)]
    (if (and (= :w scr-q) (not= :0 q)) :w q)))

(defn- check-binder-kinds!
  "A reusable field binder needs a field of kind Data: + never forms over a
  function type, so a function-typed field cannot be handed out reusable."
  [tenv ty entry arms scr-q]
  (doseq [arm (remove :catch arms)
          :let [info (get (:ctors entry) (symbol (name (:ctor arm))))
                sub (zipmap (map plain (:params entry))
                            (when (seq? ty) (rest ty)))]
          [b ft] (map vector (:binders arm) (:fields info))]
    (when (and (symbol? b)
               (= :w (effective-qty b ft scr-q))
               (not= kind/kind-Data (kind/type-kind (subst ft sub) tenv)))
      (fail! "`" b "` cannot be reusable (^:many): its field in `" ty
             "` has a function type, and a function type cannot be reused"))))

(defn- mark-binders
  "Mark each pattern binder with its effective quantity, so the quantity
  rule and later matches see it, and with its field type (the match
  type's arguments substituted), so the type checker sees it."
  [binders scr-q fields ftypes]
  (mapv (fn [b f ft]
          (let [q (effective-qty b f scr-q)
                b (vary-meta b assoc :writ/q q)]
            (if (and (some? ft) (nil? (:writ/type (meta b))))
              (vary-meta b assoc :writ/type ft)
              b)))
        binders
        (concat fields (repeat nil))
        (concat ftypes (repeat nil))))

(defn- arm-code [g tag arm]
  (if (:catch arm)
    [true (if (= '_ (:catch arm))
            (:body arm)
            (list 'let [(:catch arm) g] (:body arm)))]
    (let [ctor (:ctor arm)
          pairs (keep (fn [[b i]] (when-not (= '_ b) [b (list 'nth g (inc i))]))
                      (map vector (:binders arm) (range)))
          body (:body arm)
          test (list '= tag (keyword (str ctor)))
          taken (if (empty? pairs)
                  body
                  (list 'let (vec (mapcat identity pairs)) body))]
      [test taken])))

(defn- build-code [scrut arms]
  ;; g and tag are compiler temporaries: the expansion reads them once per
  ;; arm test, so they carry :w; the scrutinee itself is consumed once, by g.
  (let [temp (fn [s] (vary-meta (many s) assoc :writ/temp true))
        g (temp (gensym "m"))
        tag (temp (gensym "tag"))
        chain (reduce (fn [acc arm]
                        (let [[t taken] (arm-code g tag arm)]
                          (if (true? t) taken (list 'if t taken acc))))
                      nil
                      (reverse arms))]
    (list 'let [g scrut tag (list 'if (list 'vector? g) (list 'first g) g)]
          chain)))

(declare rewrite)

(defn expand
  "Check a match form against `tenv`, `scope` (name -> quantity, the names
  legal to match on) and `types` (name -> known type) and return the code
  it stands for.  Each arm body is rewritten under the scope extended with
  the pattern's binders at their effective quantities."
  ([tenv scope form] (expand tenv scope form {}))
  ([tenv scope form types]
   (when (< (count form) 4)
     (fail! "a `match` needs a scrutinee and a type: (match s :- Type arm ...)"))
   (let [s (second form)
         sep (nth form 2)
         ty (nth form 3)
         afs (drop 4 form)]
     (when-not (= ':- sep)
       (fail! "a `match` needs a type: (match s :- Type arm ...)"))
     (when-not (symbol? s)
       (fail! "the scrutinee of a `match` must be a local name, not an expression"))
     (let [scr-q (get scope (plain s))]
       (when (nil? scr-q)
         (fail! "the scrutinee of a `match` must be a parameter or a pattern "
                "binder, not a computed value"))
       (let [{:keys [entry]} (resolve-type tenv scope ty)
             ctors (:ctors entry)
             st (get types (plain s))]
         (when (and st (not (ty/compat? (ty/plain-type ty) (ty/plain-type st) tenv)))
           (fail! "`" s "` has type " (pr-str (ty/plain-type st)) ", but the match is on "
                  (pr-str (ty/plain-type ty))))
         (when (and (empty? afs) (seq ctors))
           (fail! "a `match` needs a scrutinee, a type and at least one arm: "
                  "(match s :- Type arm ...)"))
         (let [sub (zipmap (map plain (:params entry)) (when (seq? ty) (rest ty)))
               arms (mapv (fn [af]
                            (let [a (parse-arm af ctors)]
                              (if (:catch a)
                                (let [c (:catch a)
                                      c* (if (= '_ c) c
                                             (vary-meta c assoc :writ/q scr-q
                                                        :writ/type (ty/plain-type ty)))
                                      inner (if (= '_ c) scope (assoc scope (plain c) scr-q))
                                      itypes (if (= '_ c) types (assoc types (plain c) ty))]
                                  (assoc a :catch c*
                                         :body (rewrite tenv inner (:body a) itypes)))
                                (let [info (get ctors (symbol (name (:ctor a))))
                                      fts (map #(subst % sub) (:fields info))
                                      mbs (mark-binders (:binders a) scr-q (:fields info) fts)
                                      named (remove #(= '_ %) mbs)
                                      qmap (into {} (map (fn [b] [(plain b) (ann/quantity-of b)])) named)
                                      tmap (into {} (keep (fn [[b t]] (when (and t (not= '_ b))
                                                                        [(plain b) t])))
                                                 (map vector mbs fts))]
                                  (assoc a :binders mbs
                                         :body (rewrite tenv (into scope qmap) (:body a)
                                                        (into types tmap)))))))
                          afs)]
           (check-arms! ty ctors arms)
           (check-binder-kinds! tenv ty entry arms scr-q)
           (if (empty? arms)
             ;; no constructor, so no value reaches here; the result type
             ;; is whatever the context wants
             (list 'let [(vary-meta (many (gensym "m")) assoc :writ/temp true) s]
                   '(clojure.core/identity nil))
             (build-code s arms))))))))

(def ^:private binding-heads
  "Forms whose second element is a binding vector: the names they bind are
  computed values, so they leave the match scope."
  #{"let" "let*" "loop" "loop*" "when-let" "if-let" "when-some" "if-some"
    "when-first" "for" "doseq" "dotimes" "with-open" "binding" "with-redefs"})

(defn- bound-names
  "Every name a binding vector binds (destructuring and for/doseq
  modifiers included)."
  [bvec]
  (loop [xs (seq bvec), acc #{}]
    (if-not xs
      acc
      (let [b (first xs)]
        (cond
          (= :let b) (recur (nnext xs) (into acc (bound-names (second xs))))
          (keyword? b) (recur (nnext xs) acc)
          :else (recur (nnext xs) (into acc (map plain (l/binding-names b)))))))))

(defn rewrite
  "Recursively expand every match form in `form`, checking each against tenv.
  `scope` maps each matchable name to its quantity: the enclosing defn's
  parameters plus pattern binders and fn parameters introduced on the way
  down; a let/loop-style form that rebinds a name removes it.  `types`
  maps names to their known types."
  ([tenv scope form] (rewrite tenv scope form {}))
  ([tenv scope form types]
   (cond
     (seq? form)
     (cond
       (= "match" (head-name form))
       (expand tenv scope form types)

       (and (symbol? (first form)) (contains? #{"fn" "fn*"} (name (first form))))
       (let [tail (rest form)
             named? (symbol? (first tail))
             params (if named? (second tail) (first tail))
             body (if named? (drop 2 tail) (rest tail))
             ps (filter symbol? params)
             inner (into scope (map (fn [p] [(plain p) (ann/quantity-of p)])) ps)
             itypes (into (apply dissoc types (map plain ps))
                          (keep (fn [p] (when-let [t (ty/binder-type p tenv)] [(plain p) t])))
                          ps)
             rb (mapv #(rewrite tenv inner % itypes) body)]
         (if named?
           (apply list (first form) (first tail) params rb)
           (apply list (first form) params rb)))

       (and (symbol? (first form)) (contains? #{"letfn" "letfn*"} (name (first form))))
       (let [specs (second form)
             body (drop 2 form)
             inner (into scope (comp (mapcat second) (filter symbol?)
                                     (map (fn [p] [(plain p) (ann/quantity-of p)])))
                         specs)
             specs* (mapv (fn [sp]
                            (apply list (first sp) (second sp)
                                   (mapv #(rewrite tenv inner % types) (drop 2 sp))))
                          specs)
             rb (mapv #(rewrite tenv inner % types) body)]
         (apply list (first form) specs* rb))

       (and (symbol? (first form)) (contains? binding-heads (name (first form)))
            (vector? (second form)))
       (let [names (bound-names (second form))
             scope* (apply dissoc scope names)
             types* (apply dissoc types names)]
         (apply list (first form)
                (rewrite tenv scope* (second form) types*)
                (map #(rewrite tenv scope* % types*) (drop 2 form))))

       :else (apply list (map #(rewrite tenv scope % types) form)))

     (vector? form) (mapv (fn [x] (rewrite tenv scope x types)) form)
     (map? form) (into {} (map (fn [kv] [(rewrite tenv scope (first kv) types)
                                         (rewrite tenv scope (second kv) types)]) form))
     :else form)))
