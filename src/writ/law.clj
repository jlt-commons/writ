(ns writ.law
  "Laws and proofs.

    (w/law add-zero (= (+ n 0) n))
    (w/proof add-zero-refl add-zero refl)

  A law names a proposition; a proof discharges one law.  Propositions are
  built from `=`, `and`, `=>`, `forall` and `exists`; proof terms from `refl`,
  `pair`, `(fn [..] ..)` and `(witness t pf)`.  `refl` proves an equality whose
  sides are convertible (writ.norm).  The gate requires every law to be
  discharged by a proof and every proof to discharge an existing law."
  (:require [writ.norm :as norm]
            [writ.kind :as kind]
            [writ.types :as ty]))

(defn- fail! [& msg]
  (throw (ex-info (str "Writ: " (apply str msg)) {:writ/error true})))

(defn law-form?
  [f]
  (and (seq? f) (symbol? (first f)) (= "law" (name (first f)))))

(defn proof-form?
  [f]
  (and (seq? f) (symbol? (first f)) (= "proof" (name (first f)))))

(defn- bad-shape!
  [& msg]
  (throw (ex-info (str "Writ: " (apply str msg)) {:writ/error true})))

(defn- simple-sym? [x] (and (symbol? x) (nil? (namespace x))))

(defn- name-or-fail!
  [what nm]
  (if (nil? nm)
    (bad-shape! "`" what "` requires a name")
    (when-not (simple-sym? nm)
      (bad-shape! "a `" what "` name must be a simple symbol: `" nm "`")))
  nm)

(defn parse-law
  [f]
  (let [[_ nm prop] f]
    (name-or-fail! "law" nm)
    (when (nil? prop)
      (bad-shape! "law `" nm "` must carry a proposition"))
    {:name nm :prop prop}))

(defn parse-proof
  [f]
  (let [[_ nm law body] f]
    (name-or-fail! "proof" nm)
    (when (nil? law)
      (bad-shape! "proof `" nm "` must cite the law it discharges"))
    (when (nil? body)
      (bad-shape! "proof `" nm "` must carry a body"))
    {:name nm :law law :body body}))

(defn- head? [f s]
  (and (seq? f) (symbol? (first f)) (= s (name (first f)))))

(defn- fn-form? [t]
  (and (seq? t) (symbol? (first t)) (contains? #{"fn" "fn*"} (name (first t)))))

(def ^:private numeric-types '#{Nat Int Float Double})

;; --- shapes --------------------------------------------------------------

(defn check-prop-shape!
  "A proposition has an exact shape, like Bend's fixed {a == b : T}:
  (= a b), (=> P Q), (and P ...), (forall [x T] P), (exists [x T] P).
  Extra forms used to be dropped silently."
  [p]
  (cond
    (head? p "=")
    (when-not (= 3 (count p))
      (bad-shape! "Wrong number of sides to `=` in a law, had: " (dec (count p))
                  "; an equality is (= a b)"))
    (head? p "=>")
    (do (when-not (= 3 (count p))
          (bad-shape! "Wrong number of args to =>, had: " (dec (count p))
                      "; an implication is (=> P Q)"))
        (check-prop-shape! (nth p 1)) (check-prop-shape! (nth p 2)))
    (head? p "and")
    (do (when (< (count p) 2)
          (bad-shape! "`and` in a law takes at least one proposition"))
        (doseq [q (rest p)] (check-prop-shape! q)))
    (or (head? p "forall") (head? p "exists"))
    (let [[q b body & more] p]
      (when-not (and (vector? b) (= 2 (count b)) (simple-sym? (first b))
                     (some? body) (empty? more))
        (bad-shape! "`" (name q) "` must be (" (name q) " [x T] P)"))
      (check-prop-shape! body))
    :else nil))

(defn- one-param-fn
  "The param and body of a proof term `(fn [x] body)`, or nil."
  [t]
  (when (and (fn-form? t) (= 3 (count t)))
    (let [[_ ps b] t]
      (when (and (vector? ps) (= 1 (count ps)) (simple-sym? (first ps)))
        [(first ps) b]))))

;; --- substitution --------------------------------------------------------

(defn- syms [t] (into #{} (filter symbol?) (tree-seq coll? seq t)))

(defn- subst-prop
  "Substitute term `w` for variable `x` in proposition `p`.  Each equality
  side is wrapped in (let [x w] side), so writ.norm's capture-avoiding beta
  does the work inside terms; a quantifier that rebinds x stops it, and one
  whose binder occurs in `w` is renamed first so it cannot capture."
  [p x w]
  (cond
    (head? p "=") (let [[h a b] p] (list h (list 'let [x w] a) (list 'let [x w] b)))
    (head? p "and") (cons (first p) (map #(subst-prop % x w) (rest p)))
    (head? p "=>") (list (first p) (subst-prop (nth p 1) x w) (subst-prop (nth p 2) x w))
    (or (head? p "forall") (head? p "exists"))
    (let [[q [y t] body] p]
      (cond
        (= y x) p
        (contains? (syms w) y)
        (let [y* (gensym (str y "_"))]
          (list q [y* t] (subst-prop (subst-prop body y y*) x w)))
        :else (list q [y t] (subst-prop body x w))))
    :else p))

;; --- proving -------------------------------------------------------------

(declare prove)

(defn- side [t]
  (let [nf (norm/norm-form t)]
    (when (norm/throws? nf)
      (fail! "`" (pr-str t) "` throws; a law's terms must evaluate"))
    nf))

(defn- prove-eq [[_ a b] term _]
  (when-not (= 'refl term)
    (fail! "an equality is proved by `refl`"))
  (let [na (side a) nb (side b)]
    (when (or (norm/has-fn? na) (norm/has-fn? nb))
      (fail! "`" (pr-str a) "` and `" (pr-str b) "` compare fn values; Clojure's "
             "`=` on fns is identity, so refl cannot prove it (no function "
             "extensionality)"))
    (when-not (= na nb)
      (fail! "`" (pr-str a) "` and `" (pr-str b) "` are not convertible"))))

(defn- prove-and [props term ctx]
  (when-not (head? term "pair")
    (fail! "a conjunction is proved by `(pair ...)`"))
  (let [ps (rest props) ts (rest term)]
    (when (not= (count ps) (count ts))
      (fail! "`pair` gives " (count ts) " proof(s) for " (count ps)
             " proposition(s)"))
    (doseq [[p t] (map vector ps ts)] (prove p t ctx))))

(defn- prove-imp [[_ hyp concl] term ctx]
  (let [[h b] (or (one-param-fn term)
                  (fail! "an implication is proved by `(fn [h] body)`"))]
    (prove concl b (update ctx :hyps assoc h hyp))))

(defn- bind-var
  "Bring variable `y` into scope: a hypothesis that mentions a variable of
  the same name, or is named like it, is about an outer binding and no
  longer applies."
  [ctx y t]
  (-> ctx
      (update :hyps (fn [hs] (into {} (remove (fn [[k v]] (or (= k y) (contains? (syms v) y))))
                                   hs)))
      (update :numeric (fnil (if (contains? numeric-types (ty/plain-type t)) conj disj) #{}) y)))

(defn- check-domain! [t ctx]
  (kind/check-type t (or (:tenv ctx) {}) #{}))

(defn- prove-all [[_ [x t] body] term ctx]
  (let [[y b] (or (one-param-fn term)
                  (fail! "a universal is proved by `(fn [x] body)`"))]
    (check-domain! t ctx)
    (prove (if (= x y) body (subst-prop body x y)) b (bind-var ctx y t))))

(defn- prove-ex [[_ [x t] body] term ctx]
  (when-not (and (head? term "witness") (= 3 (count term)))
    (fail! "an existential is proved by `(witness t pf)`"))
  (check-domain! t ctx)
  (let [[_ w pf] term
        wt (when-not (or (symbol? w) (seq? w)) (ty/lit-type w))]
    (when (and wt (not (ty/compat? (ty/plain-type t) wt (or (:tenv ctx) {}))))
      (fail! "the witness `" (pr-str w) "` has type " wt ", not " t))
    (prove (subst-prop body x w) pf ctx)))

(defn- prop-canon
  "A proposition with its quantifier binders renamed by depth and its
  equality sides normalised: two props are the same law iff these match."
  [p depth]
  (cond
    (head? p "=") (list '= (side (nth p 1)) (side (nth p 2)))
    (head? p "and") (cons 'and (map #(prop-canon % depth) (rest p)))
    (head? p "=>") (list '=> (prop-canon (nth p 1) depth) (prop-canon (nth p 2) depth))
    (or (head? p "forall") (head? p "exists"))
    (let [[q [y t] body] p
          y* (symbol (str "q%" depth))]
      (list (symbol (name q)) (ty/plain-type t)
            (prop-canon (subst-prop body y y*) (inc depth))))
    :else p))

(defn prove
  "Check that `term` proves proposition `goal`.  ctx holds :laws (name ->
  proposition, the laws already proved), :hyps (name -> proposition,
  hypotheses in scope), :numeric (variables of a numeric type) and :tenv.
  Returns true or throws."
  [goal term ctx]
  (binding [norm/*numeric* (or (:numeric ctx) #{})]
    (cond
      (and (symbol? term) (or (contains? (:hyps ctx) term) (contains? (:laws ctx) term)))
      (let [cited (if (contains? (:hyps ctx) term) (get (:hyps ctx) term) (get (:laws ctx) term))]
        (when-not (= (prop-canon cited 0) (prop-canon goal 0))
          (fail! "`" term "` proves `" cited "`, not `" goal "`"))
        true)

      (head? goal "=")      (prove-eq goal term ctx)
      (head? goal "and")    (prove-and goal term ctx)
      (head? goal "=>")     (prove-imp goal term ctx)
      (head? goal "forall") (prove-all goal term ctx)
      (head? goal "exists") (prove-ex goal term ctx)
      :else (fail! "cannot prove `" goal "` by `" term "`"))))

(defn discharge
  "Check one proof against the law it names, under the laws already proved
  (`proved`, name -> prop).  A citation names a law and must reference one
  whose own proof appeared earlier, so proofs are never citable and citation
  cycles cannot form.  Returns the law name."
  [{:keys [name law body]} laws proved tenv]
  (let [l (get laws law)]
    (when (nil? l)
      (fail! "proof `" name "` discharges no law: `" law "` is not declared"))
    (when (contains? proved law)
      (fail! "proof `" name "` re-proves law `" law "`: a law is discharged once"))
    (doseq [s (tree-seq coll? seq body)]
      (when (and (symbol? s) (contains? laws s) (not (contains? proved s)))
        (fail! "proof `" name "` cites law `" s "` before it is proved: laws "
               "are cited in proof order, after their own proof")))
    (check-prop-shape! (:prop l))
    (prove (:prop l) body {:laws proved :hyps {} :numeric #{} :tenv tenv})
    law))

(defn gate
  "Run the law/proof gate, in book order.  laws is name -> decl; proofs is a
  seq of decls in file order.  A proof may cite a law only if that law's
  proof appeared earlier."
  ([laws proofs] (gate laws proofs {}))
  ([laws proofs tenv]
   (loop [ps proofs, proved {}]
     (if-let [p (first ps)]
       (recur (rest ps)
              (let [nm (discharge p laws proved tenv)]
                (assoc proved nm (:prop (get laws (:law p))))))
       (let [open (remove (set (keys proved)) (keys laws))]
         (when (seq open)
           (fail! "law `" (first open) "` is not filled: no proof discharges it")))))
   {:ok true :laws (vec (keys laws))}))
