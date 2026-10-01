(ns writ.prove.symbolic
  "Symbolic evaluation of a goal into one formula for writ.solve.

  Rewriting a goal splits it at every if, and a step fn with a dozen
  conditions makes thousands of cases.  Here the goal is run once, on
  symbolic values, the way Rosette runs a program: the two branches of an
  if are both run, and their values are merged under the test.  Merging
  keeps the result small -- two integers merge into one, defined once as
  an if of the two, two vectors of one length merge element by element --
  and only values of different shapes, a data value whose constructor
  depends on the branch, are kept apart, as a union of guarded values.

  A value is one of

    {:int t}           an integer, t a solver term
    {:bool f}          true or false, f a solver formula
    {:const t}         a keyword, string, char or symbol, t its code;
                       :ctype :keyword, :string, :char or :symbol when it
                       is known which
    {:nil}
    {:vec [v ...]}     a sequential value of known length; :kind :vector
                       when it is known to be a vector, :seq when it is
                       known not to be, absent when either may be
    {:opaque t}        a value of type Any that is none of the shapes
                       here: a double, a map, a collection of unknown
                       length.  It can only be passed along and compared
                       with another opaque value (t is its code); any
                       other use of it gives up
    {:map [[p k v] ...]}  a map: entry k -> v is in it when formula p
                       holds; the keys of the entries present are distinct,
                       so a lookup, an assoc and equality need no search.
                       Keys may be symbolic.  Its entries have no order, as
                       a Clojure map's do not: keys and vals are seqs drawn
                       from a set.  :rest r marks a record's value, which
                       may hold keys its record does not name, r standing
                       for them: a lookup, an assoc or a dissoc of a key it
                       does not name, anything that walks every entry, and
                       equality with a map of another rest give up
    {:set {...}}       a set, or a seq drawn from one: :mem gives the
                       formula for 'x is in it'; :elems, when it is
                       finite, its elements as [guard v]; :elem a value
                       shaped like its elements
    {:fn f}            a fn value: f takes a vector of values
    {:union [[g v] ...]}  v where formula g holds; the gs are disjoint
    :bottom            a throw

  A set of unknown size -- a variable of type (Set T) -- is a predicate
  the solver knows nothing about: x is in it when the predicate holds of
  x.  The image of such a set under a translation, a fn adding a fixed
  offset to each part of an element, is the predicate at x minus the
  offset.  Two sets are equal when an element the solver may choose
  freely is in both or in neither: extensionality, read the same way in a
  goal or a hypothesis.

  A constant's code is fixed per distinct literal; a variable of a type
  of constants is an integer the solver may give any value, so it may
  equal any literal, or none.  That can only add models, never remove
  one, so a formula found valid holds of the code.

  What is outside -- recursion, collections of unknown length, fns as
  values -- makes the evaluation give up, and the goal is left to the
  rest of the prover.  Proofs are for every input on which the terms
  return: a branch that throws is never taken, so merging it with a value
  is that value.

  `formula` is deterministic, so the proof checker rebuilds it and checks
  the solver's certificate for it."
  (:require [writ.prove.term :as t :refer [head]]
            [writ.solve :as solve]))

(def ^:dynamic *why*
  "When bound to an atom, collects why evaluations gave up, for debugging."
  nil)

(defn- give-up! [why]
  (throw (ex-info (str "outside symbolic evaluation: " why) {::outside why})))

;; --- state: fresh names, definitions and constant codes -------------------------

(defn- state []
  (atom {:n 0 :defs [] :decls {} :codes {} :memo {} :path [] :throws []}))

(def ^:private max-vars
  "How many variables one goal's evaluation may make before it gives up:
  a value of unknown shape taken apart level by level multiplies its
  alternatives, and the formula it grows would swamp the solver anyway."
  20000)

(defn- fresh! [st kind]
  (let [n (:n @st)
        _ (when (>= n max-vars)
            (throw (ex-info "outside symbolic evaluation: too large a formula"
                            {::outside "too large a formula" ::spent true})))
        s (symbol (str "%" (name kind) n))]
    (swap! st #(-> % (update :n inc) (assoc-in [:decls s] kind)))
    s))

(defn- define!
  "A fresh variable standing for integer term or formula e."
  [st kind e]
  (if (or (symbol? e) (integer? e) (boolean? e))
    e
    (let [v (fresh! st kind)]
      (swap! st #(-> % (update :defs conj (if (= :int kind) [:= v e] [:iff v e]))
                     (assoc-in [:def-of v] e)))
      v)))

(defn- interval
  "[lo hi] an integer term lies in, nil for no bound on that side: from
  its literals, the bounds its variables are known to have, and the
  definitions of the variables merging introduced."
  [st t]
  (let [iv #(interval st %)
        add (fn [[a b] [c d]] [(when (and a c) (+ a c)) (when (and b d) (+ b d))])
        neg (fn [[a b]] [(when b (- b)) (when a (- a))])
        lo-of (fn [xs] (when (every? some? xs) (apply min xs)))
        hi-of (fn [xs] (when (every? some? xs) (apply max xs)))]
    (cond
      (integer? t) [t t]
      (symbol? t) (if-let [d (get-in @st [:def-of t])]
                    (iv d)
                    (get-in @st [:bounds t] [nil nil]))
      (vector? t)
      (let [[op & xs] t]
        (case op
          :+ (reduce add [0 0] (map iv xs))
          :- (if (next xs) (reduce add (iv (first xs)) (map (comp neg iv) (rest xs))) (neg (iv (first xs))))
          :neg (neg (iv (first xs)))
          :* (let [[k u] xs [a b] (iv u)]
               (if (integer? k)
                 (if (neg? k) [(when b (* k b)) (when a (* k a))] [(when a (* k a)) (when b (* k b))])
                 [nil nil]))
          :ite (let [[a b] (iv (nth xs 1)) [c d] (iv (nth xs 2))] [(lo-of [a c]) (hi-of [b d])])
          :min (let [[a b] (iv (first xs)) [c d] (iv (second xs))] [(lo-of [a c]) (cond (and b d) (min b d) b b :else d)])
          :max (let [[a b] (iv (first xs)) [c d] (iv (second xs))] [(cond (and a c) (max a c) a a :else c) (hi-of [b d])])
          :mod (let [k (second xs)] (if (pos? k) [0 (dec k)] [(inc k) 0]))
          [nil nil]))
      :else [nil nil])))

(defn- code!
  "The integer code of a constant literal: distinct literals, distinct codes."
  [st c]
  (or (get-in @st [:codes c])
      (let [k (- -1000000 (count (:codes @st)))]
        (swap! st assoc-in [:codes c] k)
        k)))

;; --- values ---------------------------------------------------------------------

(defn- const? [x] (or (keyword? x) (string? x) (char? x) (symbol? x)))

(defn- ctype-of
  "Which kind of constant x is."
  [x]
  (cond (keyword? x) :keyword (string? x) :string (char? x) :char (symbol? x) :symbol))

(defn- lit-value [st x]
  (cond
    (nil? x) {:nil true}
    (boolean? x) {:bool x}
    (integer? x) {:int x}
    (const? x) {:const (code! st x) :ctype (ctype-of x)}
    :else (give-up! (str "the literal " (pr-str x)))))

(defn- alts
  "A value as guarded alternatives."
  [v]
  (cond (= :bottom v) []
        (:union v) (:union v)
        :else [[true v]]))

(defn- conj-f [a b]
  (cond (true? a) b (true? b) a (or (false? a) (false? b)) false :else [:and a b]))

(defn- shape [v]
  (cond (:int v) :int (contains? v :int) :int
        (contains? v :bool) :bool
        (contains? v :const) :const
        (:nil v) :nil
        (:vec v) [:vec (count (:vec v))]
        (:set v) :set
        (:map v) [:map (mapv second (:map v))]
        (:fn v) :fn
        (contains? v :opaque) :opaque
        :else (give-up! "a value of no known shape")))

(defn- merge-key
  "What must agree for two values to merge into one: their shape, and a
  constant's kind, so that the kinds of an Any stay apart."
  [v]
  (if (contains? v :const) [:const (:ctype v)] (shape v)))

(declare merge-values)

(defn- merge-maps
  "Two maps with the same keys, merged under c entry by entry."
  [st c a b]
  (when (not= (:rest a) (:rest b)) (give-up! "two maps, one holding keys its record does not name"))
  (cond-> {:map (mapv (fn [[p k v] [q _ w]]
                        [(define! st :bool [:or [:and c p] [:and [:not c] q]]) k (merge-values st c v w)])
                      (:map a) (:map b))}
    (:rest a) (assoc :rest (:rest a))))

(defn- merge-same
  "Merge two values of one shape under formula c."
  [st c a b]
  (cond
    (:map a) (merge-maps st c a b)
    (contains? a :const) (cond-> {:const (define! st :int [:ite c (:const a) (:const b)])}
                           (and (:ctype a) (= (:ctype a) (:ctype b))) (assoc :ctype (:ctype a)))
    :else
  (case (shape a)
    :int {:int (define! st :int [:ite c (:int a) (:int b)])}
    :const (cond-> {:const (define! st :int [:ite c (:const a) (:const b)])}
             (and (:ctype a) (= (:ctype a) (:ctype b))) (assoc :ctype (:ctype a)))
    :bool {:bool (define! st :bool [:or [:and c (:bool a)] [:and [:not c] (:bool b)]])}
    :nil a
    :opaque {:opaque (define! st :int [:ite c (:opaque a) (:opaque b)])}
    :set (let [sa (:set a) sb (:set b)]
           {:set {:mem (fn [x] [:or [:and c ((:mem sa) x)] [:and [:not c] ((:mem sb) x)]])
                  :elems (when (and (:elems sa) (:elems sb))
                           (vec (concat (for [[g v] (:elems sa)] [(conj-f c g) v])
                                        (for [[g v] (:elems sb)] [(conj-f [:not c] g) v]))))
                  :distinct (and (:distinct sa) (:distinct sb))
                  :elem (or (:elem sa) (:elem sb))}})
    ;; the same named fn either way is that fn
    :fn (if (and (:named a) (= (:named a) (:named b))) a (give-up! "a fn value chosen by a test"))
    (cond-> {:vec (mapv #(merge-values st c %1 %2) (:vec a) (:vec b))}
      (and (:kind a) (= (:kind a) (:kind b))) (assoc :kind (:kind a))))))

(defn- union-of
  "A value from guarded alternatives, alternatives of one shape merged."
  [st gvs]
  (let [gvs (for [[g v] gvs
                  [g2 v2] (alts v)
                  :let [g* (conj-f g g2)]
                  :when (not (false? g*))]
              [g* v2])]
    (cond
      (empty? gvs) :bottom
      (= 1 (count gvs)) (second (first gvs))
      :else
      (let [groups (vals (group-by (comp merge-key second) gvs))
            merged (for [g groups]
                     (reduce (fn [[ga va] [gb vb]]
                               [[:or ga gb] (merge-same st ga va vb)])
                             g))]
        (if (= 1 (count merged))
          (second (first merged))
          {:union (vec merged)})))))

(defn merge-values
  "The value that is a when c holds and b otherwise."
  [st c a b]
  (cond
    (true? c) a
    (false? c) b
    (= :bottom a) b
    (= :bottom b) a
    (and (not (:union a)) (not (:union b)) (= (merge-key a) (merge-key b))) (merge-same st c a b)
    :else (union-of st (concat (for [[g v] (alts a)] [(conj-f c g) v])
                               (for [[g v] (alts b)] [(conj-f [:not c] g) v])))))

(defn- throws!
  "Clojure throws here: arithmetic on nil, first of a number."
  []
  (throw (ex-info "throws" {::throws true})))

(defn- record-throw!
  "Note that evaluation throws when formula g holds on the current path."
  [st g]
  (when-not (false? g)
    (swap! st update :throws conj (reduce conj-f g (:path @st)))))

(defn- on-path
  "(f), with formula c added to the path the evaluation is on."
  [st c f]
  (swap! st update :path conj c)
  (try (f) (finally (swap! st update :path pop))))

(defn- relevant-defs
  "The definitions and facts formulas fs depend on: those of the variables
  they mention, and of the variables those definitions mention, and so on
  (constraint independence, as KLEE splits a query).  The rest constrain
  only variables fs never reach, so leaving them out cannot turn a
  satisfiable question unsatisfiable, and a refutation without them
  refutes with them."
  [st fs]
  (let [{:keys [defs def-of]} @st
        vars-of (fn [f] (filter symbol? (tree-seq coll? seq f)))
        cone (loop [todo (vec (mapcat vars-of fs)) seen #{}]
               (if-let [v (peek todo)]
                 (if (contains? seen v)
                   (recur (pop todo) seen)
                   (recur (into (pop todo) (some-> (get def-of v) vars-of)) (conj seen v)))
                 seen))]
    (filterv (fn [d] (some cone (vars-of d))) defs)))

(def ^:private max-prune-size
  "The most definitions and path conditions a branch is pruned under."
  400)

(defn- unreachable?
  "Is the path the evaluation is on impossible, under what the goal assumes
  -- its hypotheses, its variables' facts and the definitions so far?  Asked
  of the solver, with a small budget: :unsat, :sat or :unknown."
  [st]
  (let [{:keys [assumed path decls]} @st
        defs (relevant-defs st (concat assumed path))]
    ;; a large formula is not asked about: the solver's budget bounds its
    ;; search, not the work of reading the formula in, and pruning only
    ;; ever buys completeness
    (if (<= (+ (count assumed) (count defs) (count path)) max-prune-size)
      (case (:result (try (solve/check (into [:and true] (concat assumed defs path)) decls {:budget 2000})
                          (catch clojure.lang.ExceptionInfo _ nil)))
        :unsat :unsat
        :sat :sat
        :unknown)
      :unknown)))

(defn- pruned
  "(thunk), unless it gives up on a path no model reaches: that branch is
  never taken, so its value is :bottom and the evaluation goes on.  Only a
  give-up is pruned, and only on a path the solver refutes, so what is left
  is the code's meaning wherever it can run."
  [st thunk]
  (try (thunk)
       (catch clojure.lang.ExceptionInfo e
         (let [d (ex-data e)]
           (cond
             (or (not (::outside d)) (::spent d) (::reachable d)) (throw e)
             :else
             (case (unreachable? st)
               :unsat :bottom
               ;; the paths of the pruned calls around this one are shorter,
               ;; so reachable too: none of them asks again
               :sat (throw (ex-info (ex-message e) (assoc d ::reachable true) e))
               (throw e)))))))

(defn- guarded
  "(f x), or :bottom where Clojure would throw, noting that it does."
  [st f x]
  (try (f x)
       (catch clojure.lang.ExceptionInfo e
         (if (::throws (ex-data e))
           (do (record-throw! st true) :bottom)
           (throw e)))))

(defn- lift
  "Apply f to each alternative of v, merging the results; an alternative
  on which Clojure throws is never taken, and the throw is noted."
  [st f v]
  (if (:union v)
    (union-of st (vec (for [[g x] (:union v)] [g (on-path st g #(pruned st (fn [] (guarded st f x))))])))
    (if (= :bottom v) :bottom (guarded st f v))))

(defn- lift2 [st f a b]
  (lift st (fn [x] (lift st (fn [y] (f x y)) b)) a))

(defn truth
  "The formula for 'v is truthy'."
  [v]
  (cond
    (= :bottom v) true
    (:union v) (into [:or] (for [[g x] (:union v)] (conj-f g (truth x))))
    (contains? v :bool) (:bool v)
    (:nil v) false
    :else true))

(defn- int-of
  "The integer of v; arithmetic on anything else throws in Clojure."
  [v]
  (cond (contains? v :int) (:int v)
        (contains? v :opaque) (give-up! "arithmetic on a value of type Any")
        :else (throws!)))

(declare equal fold unknown!)

(defn- fresh-like
  "A value shaped like v, of fresh variables the solver may choose."
  [st v]
  (when (:map v) (give-up! "a set of maps"))
  (if (contains? v :const)
    (cond-> {:const (fresh! st :int)} (:ctype v) (assoc :ctype (:ctype v)))
  (case (shape v)
    :int {:int (fresh! st :int)}
    :const (cond-> {:const (fresh! st :int)} (:ctype v) (assoc :ctype (:ctype v)))
    :bool {:bool (fresh! st :bool)}
    :nil v
    :opaque {:opaque (fresh! st :int)}
    :set (give-up! "a set of sets")
    :fn (give-up! "a set of fns")
    {:vec (mapv #(fresh-like st %) (:vec v))})))

(defn- flat
  "The solver terms of an element, part by part, or nil when it has a
  part no predicate can take."
  [v]
  (cond (contains? v :int) [(:int v)]
        (contains? v :const) [(:const v)]
        (:vec v) (let [ps (map flat (:vec v))] (when (every? some? ps) (vec (apply concat ps))))
        :else nil))

(defn- member-of
  "The formula for 'x is one of these guarded elements'."
  [st elems x]
  (into [:or false] (for [[g v] elems] (conj-f g (truth (lift2 st (fn [p q] {:bool (equal st p q)}) x v))))))

(defn- finite-set
  "A set of guarded elements; distinct when it is a set, not a seq drawn
  from one, so equal elements count once."
  [st elems distinct]
  {:set {:mem (fn [x] (member-of st elems x))
         :elems (vec elems)
         :distinct distinct
         :elem (second (first elems))}})

(defn- ordered
  "A seq of guarded elements es, in order: each element there when its
  guard holds.  It compares with a seq as a seq does."
  [st es]
  (assoc-in (finite-set st es false) [:set :ordered] true))

(defn- guarded-elems
  "The guarded elements of a seq whose order is known, or nil."
  [v]
  (cond (:vec v) (mapv (fn [x] [true x]) (:vec v))
        (and (:set v) (:ordered (:set v))) (:elems (:set v))
        :else nil))

(defn- one-if [c] (if (true? c) 1 (if (false? c) 0 [:ite c 1 0])))

(defn- ranks
  "Each element's place among the kept ones: how many kept elements come
  before it."
  [es]
  (mapv (fn [i] (into [:+ 0] (map (comp one-if first) (take i es)))) (range (count es))))

(declare map-equal)

(defn- equal
  "The formula for (= a b)."
  [st a b]
  (let [sa (shape a) sb (shape b)]
    (cond
      ;; maps are equal by their entries, whatever the entries' order or
      ;; how each was built, so shape says nothing between two of them
      (and (:map a) (:map b)) (map-equal st a b)
      (or (and (:map a) (contains? b :opaque)) (and (:map b) (contains? a :opaque)))
      (give-up! "comparing a map with a value of type Any")
      (or (:map a) (:map b)) false
      ;; a filtered seq and a seq, or two filtered seqs: equal when as many
      ;; are kept and the kept ones agree place by place
      (and (or (:ordered (:set a)) (:ordered (:set b))) (guarded-elems a) (guarded-elems b))
      (let [as (guarded-elems a) bs (guarded-elems b)
            ra (ranks as) rb (ranks bs)
            n (fn [es] (into [:+ 0] (map (comp one-if first) es)))]
        (reduce conj-f [:= (n as) (n bs)]
                (for [i (range (count as)) j (range (count bs))]
                  [:or [:not (conj-f (conj-f (first (nth as i)) (first (nth bs j))) [:= (nth ra i) (nth rb j)])]
                   (let [x (second (nth as i)) y (second (nth bs j))]
                     (if (= x y) true (truth (lift2 st (fn [p q] {:bool (equal st p q)}) x y))))])))
      ;; a seq whose order the model does not know, such as a map's vals,
      ;; against a seq: outside
      (or (and (:set a) (not (:distinct (:set a))) (:vec b))
          (and (:set b) (not (:distinct (:set b))) (:vec a)))
      (give-up! "comparing a seq of unknown order with a seq")
      ;; an opaque value is none of int, constant, bool or nil, but it may
      ;; be a collection, so only against those is it known to differ
      (and (not= sa sb) (or (= :opaque sa) (= :opaque sb))
           (let [other (if (= :opaque sa) b a)]
             (not (or (contains? other :int) (contains? other :const)
                      (contains? other :bool) (:nil other)))))
      (give-up! "comparing a value of type Any with a collection")
      (not= sa sb) false
      (= :opaque sa) [:= (:opaque a) (:opaque b)]
      ;; two literals compare now, so an if on them runs only its branch
      (and (= :int sa) (integer? (fold (:int a))) (integer? (fold (:int b))))
      (= (fold (:int a)) (fold (:int b)))
      (and (contains? a :const) (integer? (:const a)) (integer? (:const b))) (= (:const a) (:const b))
      ;; a keyword is never a symbol, whatever codes the solver picks
      (and (contains? a :const) (:ctype a) (:ctype b) (not= (:ctype a) (:ctype b))) false
      (= :int sa) [:= (:int a) (:int b)]
      (contains? a :const) [:= (:const a) (:const b)]
      (= :bool sa) [:iff (:bool a) (:bool b)]
      (= :nil sa) true
      (= :set sa) (let [tmpl (or (:elem (:set a)) (:elem (:set b)))]
                    (if (nil? tmpl)
                      true
                      (let [x (fresh-like st tmpl)]
                        [:iff ((:mem (:set a)) x) ((:mem (:set b)) x)])))
      (= :fn sa) (give-up! "equality of fns")
      :else (reduce conj-f true (map (fn [x y] (if (= x y) true (truth (lift2 st (fn [p q] {:bool (equal st p q)}) x y))))
                                     (:vec a) (:vec b))))))

;; --- maps ---------------------------------------------------------------------------

(defn- same-key
  "The formula for (= k1 k2) of two keys."
  [st k1 k2]
  (if (= k1 k2) true (truth (lift2 st (fn [p q] {:bool (equal st p q)}) k1 k2))))

(defn- named!
  "Give up on key k of a record's value when its record does not name it:
  the keys it does not name may hold it."
  [m k]
  (when (and (:rest m) (not-any? #(= k (second %)) (:map m)))
    (give-up! "a key a record does not name")))

(defn- open!
  "Give up on walking every entry of a record's value."
  [m what]
  (when (:rest m) (give-up! (str what " of a record, which may hold keys it does not name"))))

(defn- map-equal
  "Two maps are equal when each has every entry the other has."
  [st a b]
  (when (not= (:rest a) (:rest b))
    (give-up! "comparing a record's value with a map that may not hold the same other keys"))
  (let [covers (fn [m n]
                 (reduce conj-f true
                         (for [[p k v] (:map m)]
                           [:or [:not p]
                            (into [:or false]
                                  (for [[q k2 w] (:map n)]
                                    (conj-f q (conj-f (same-key st k k2)
                                                      (if (= v w) true (truth (lift2 st (fn [x y] {:bool (equal st x y)}) v w)))))))])))]
    (conj-f (covers a b) (covers b a))))

(defn- map-lookup
  "The value of key k in map m, or dflt."
  [st m k dflt]
  (named! m k)
  (reduce (fn [acc [p k2 v]]
            (merge-values st (define! st :bool (conj-f p (same-key st k k2))) v acc))
          dflt (reverse (:map m))))

(defn- map-without
  "m with the entry for k gone, when present-if holds."
  [st m k present-if]
  (named! m k)
  (assoc m :map (vec (for [[p k2 v] (:map m)]
                       [(define! st :bool (conj-f p [:not (conj-f present-if (same-key st k k2))])) k2 v]))))

(defn- map-assoc
  "m with k -> v, when present-if holds: the old entry for k, if any, gone."
  [st m k v present-if]
  (update (map-without st m k present-if) :map conj [present-if k v]))

(defn- as-map
  "A map value, nil as the empty map; anything else is outside."
  [x]
  (cond (:map x) x
        (:nil x) {:map []}
        :else (give-up! "a map operation on a value that is not a map")))

;; --- evaluating terms -------------------------------------------------------------

(declare ev app apply-fn image core* finite-set)

(defn- var-value
  "The value of a variable of type ty: fresh solver variables, and the
  facts its type gives, such as a Nat at least 0."
  [st facts ty tenv v]
  (let [ty (if (seq? ty) (apply list (map #(if (symbol? %) (symbol (name %)) %) ty))
               (if (symbol? ty) (symbol (name ty)) ty))]
    (cond
      (= 'Int ty) {:int (fresh! st :int)}
      (= 'Nat ty) (let [x (fresh! st :int)]
                    (swap! facts conj [:<= 0 x])
                    (swap! st assoc-in [:bounds x] [0 nil])
                    {:int x})
      (= 'Bool ty) {:bool (fresh! st :bool)}
      (contains? '#{Keyword String Char Symbol} ty)
      {:const (fresh! st :int) :ctype ('{Keyword :keyword String :string Char :char Symbol :symbol} ty)}
      ;; any value: an integer, a constant, a boolean, nil, or something
      ;; else, opaque -- every value is one of these, so a formula valid
      ;; over the five holds of every value
      (= 'Any ty)
      ;; a constant is one of the four kinds, each its own alternative, so a
      ;; symbol? or keyword? of it is decided with the kind
      (let [tag (fresh! st :int)]
        (swap! facts conj [:<= 0 tag 7])
        (union-of st [[[:= tag 0] {:int (fresh! st :int)}]
                      [[:= tag 1] {:const (fresh! st :int) :ctype :keyword}]
                      [[:= tag 2] {:const (fresh! st :int) :ctype :symbol}]
                      [[:= tag 3] {:const (fresh! st :int) :ctype :string}]
                      [[:= tag 4] {:const (fresh! st :int) :ctype :char}]
                      [[:= tag 5] {:bool (fresh! st :bool)}]
                      [[:= tag 6] {:nil true}]
                      [[:= tag 7] {:opaque (fresh! st :int)}]]))
      (and (seq? ty) (= 'Tuple (first ty)))
      {:vec (mapv #(var-value st facts % tenv v) (rest ty))}
      ;; a T or nil
      (and (seq? ty) (= 'Opt (first ty)) (= 2 (count ty)))
      (let [c (fresh! st :bool)]
        (union-of st [[c {:nil true}] [[:not c] (var-value st facts (second ty) tenv v)]]))
      ;; a record: an entry per key, an (Opt T) key's there only when its
      ;; flag says so; and keys the record does not name, unknown
      (and (map? ty) (seq ty) (every? keyword? (keys ty)))
      {:map (vec (for [[k kt] (sort-by (comp str key) ty)
                       :let [opt? (and (seq? kt) (= 'Opt (first kt)))]]
                   [(if opt? (fresh! st :bool) true)
                    {:const (code! st k) :ctype :keyword}
                    (var-value st facts kt tenv v)]))
       :rest (fresh! st :int)}
      ;; a vector of unknown length: opaque, but known to be a vector, so
      ;; (vector? v) is true of it and a law that only passes it along is
      ;; decided without its elements; reading them gives up, as for Any
      (and (seq? ty) (= 'Vec (first ty)))
      (let [x {:opaque (fresh! st :int)}]
        (swap! st #(-> %
                       (assoc-in [:unknowns ['vector? x]] true)
                       (assoc-in [:unknowns ['sequential? x]] true)
                       (assoc-in [:unknowns ['map? x]] false)))
        x)
      ;; any seq, nil among them: opaque, so a law that only passes it
      ;; along, or a record that holds one, is decided without it; reading
      ;; it gives up
      (and (seq? ty) (= 'List (first ty)))
      {:opaque (fresh! st :int)}
      (and (seq? ty) (= 'Set (first ty)))
      (let [tmpl (var-value st (atom []) (second ty) tenv v)
            n (count (or (flat tmpl) (give-up! (str "a set of " (pr-str (second ty))))))
            p (fresh! st :pred)]
        (swap! st assoc-in [:decls p] [:pred n])
        {:set {:pred p
               :mem (fn [x] (if-let [ts (flat x)]
                              (if (= n (count ts)) (into [:papp p] ts) false)
                              false))
               :elem tmpl}})
      (and (symbol? ty) (get-in tenv [ty :ctors]) (empty? (:params (get tenv ty))))
      (let [ctors (sort-by str (keys (get-in tenv [ty :ctors])))
            tag (fresh! st :int)]
        (when (some (fn [c] (some #(= ty (if (symbol? %) (symbol (name %)) %))
                                  (get-in tenv [ty :ctors c :fields])))
                    ctors)
          (give-up! (str "the recursive data type " ty)))
        (swap! facts conj [:<= 0 tag (dec (count ctors))])
        (union-of st (map-indexed
                       (fn [i c]
                         [[:= tag i]
                          {:vec (into [{:const (code! st (keyword (str c))) :ctype :keyword}]
                                      (map #(var-value st facts % tenv v)
                                           (get-in tenv [ty :ctors c :fields])))
                           :kind :vector}])
                       ctors)))
      :else (give-up! (str "a variable `" v "` of type " (pr-str ty))))))


(defn- elems
  "The seq value of an element list: {:vec values}, a seq of guarded
  elements when a part is a filtered seq, or alternatives of such; give
  up when a part's length or order is unknown."
  [st env e]
  (let [join (fn [x y]
               (lift2 st (fn [x y]
                           (cond (and (:vec x) (:vec y)) {:vec (into (:vec x) (:vec y))}
                                 (and (guarded-elems x) (guarded-elems y))
                                 (ordered st (concat (guarded-elems x) (guarded-elems y)))
                                 :else (give-up! "the elements of a value of unknown length")))
                      x y))]
    (case (head e)
      :enil {:vec []}
      :econs (join {:vec [(ev st env (nth e 1))]} (elems st env (nth e 2)))
      :eapp (join (elems st env (nth e 1)) (elems st env (nth e 2)))
      :elems (lift st (fn [v]
                        (cond (:vec v) {:vec (:vec v)}
                              (:nil v) {:vec []}
                              (guarded-elems v) v
                              :else (give-up! "the elements of a value of unknown length")))
                   (ev st env (second e)))
      (give-up! "an element list of unknown length"))))

(defn- seq-of
  "The elements of a seqable value, as a vector of values; nil has none,
  and a number, keyword or boolean is not seqable, so Clojure throws."
  [v]
  (cond (:vec v) (:vec v)
        (:nil v) []
        (:set v) (give-up! "the order of a set's elements")
        (:fn v) (throws!)
        (contains? v :opaque) (give-up! "the elements of a value of type Any")
        (:map v) (give-up! "the order of a map's entries")
        :else (throws!)))

(defn- opaque? [v] (contains? v :opaque))

(defn- decided
  "A comparison of two literal integers, decided: [:> 4 0] is true, so an
  if on it runs one branch."
  [[op a b :as f]]
  (let [a (fold a) b (fold b)]
    (if (and (integer? a) (integer? b) (contains? #{:< :<= :> :>= :=} op))
      (case op :< (< a b) :<= (<= a b) :> (> a b) :>= (>= a b) := (= a b))
      f)))

(defn- num-test
  "The formula of a numeric test of vs.  On an opaque value -- a double, or
  a value it throws on -- the test is some boolean the solver may choose:
  that only adds models, so a formula valid over them holds."
  [st op vs f]
  (if (some opaque? vs) (unknown! st op vs :bool) (decided (f))))

(defn- compare-int [op a b]
  [op (int-of a) (int-of b)])

(defn- fold
  "An integer term with its literal parts computed: [:+ 1 2] is 3."
  [t]
  (if (vector? t)
    (let [[op & xs] t
          xs (map #(if (keyword? %) % (fold %)) xs)]
      (if (and (contains? #{:+ :- :* :neg :quot :mod :abs :max :min} op) (every? integer? xs))
        (case op
          :+ (apply + xs) :- (apply - xs) :* (apply * xs) :neg (- (first xs))
          :quot (quot (first xs) (second xs)) :mod (mod (first xs) (second xs))
          :abs (abs (first xs)) :max (apply max xs) :min (apply min xs))
        (into [op] xs)))
    t))

(defn- concrete
  "The Clojure value of a symbolic value made only of literals, or ::none."
  [st v]
  (let [by-code (into {} (map (fn [[c k]] [k c])) (:codes @st))]
    ((fn walk [v]
       (cond
         ;; a throw, or anything else that is no value's description
         (not (map? v)) ::none
         (and (contains? v :int) (integer? (:int v))) (:int v)
         (and (contains? v :bool) (boolean? (:bool v))) (:bool v)
         (and (contains? v :const) (contains? by-code (:const v))) (by-code (:const v))
         (:nil v) nil
         ;; str, pr-str and = on a coll see a vector from a seq, so a
         ;; value of unknown kind is no one value
         (:vec v) (let [xs (mapv walk (:vec v))]
                    (cond (some #{::none} xs) ::none
                          (= :vector (:kind v)) xs
                          (= :seq (:kind v)) (apply list xs)
                          :else ::none))
         (and (:set v) (:elems (:set v)) (every? (comp true? first) (:elems (:set v))))
         (let [xs (mapv (comp walk second) (:elems (:set v)))] (if (some #{::none} xs) ::none (set xs)))
         :else ::none))
     v)))

(defn- from-concrete
  "The symbolic value of a plain Clojure value, or nil."
  [st x]
  (cond (sequential? x) (let [vs (map #(from-concrete st %) x)]
                          (when (every? some? vs) {:vec (vec vs) :kind (if (vector? x) :vector :seq)}))
        (set? x) (let [vs (map #(from-concrete st %) x)]
                   (when (every? some? vs) (finite-set st (map (fn [v] [true v]) vs) true)))
        (map? x) (let [es (map (fn [[k v]] [(from-concrete st k) (from-concrete st v)]) (sort-by (comp pr-str key) x))]
                   (when (every? #(every? some? %) es)
                     {:map (mapv (fn [[k v]] [true k v]) es)}))
        (fn? x) nil
        :else (try (lit-value st x) (catch clojure.lang.ExceptionInfo _ nil))))

(defn- unknown!
  "What op answers of v, where the model does not know: a fresh variable of
  kind the solver may choose, the same one each time op is asked of the same
  value -- (vector? x) in a hypothesis and in the code are one answer, as an
  uninterpreted fn's are (Ackermann)."
  [st op v kind]
  (let [k [op v]]
    ;; an answer already given may be false, so look it up by presence
    (if (contains? (:unknowns @st) k)
      (get-in @st [:unknowns k])
      (let [x (fresh! st kind)]
        (swap! st assoc-in [:unknowns k] x)
        x))))

(defn- kind-is?
  "The formula for 'v is a vector'.  Where that is not known -- a sequence
  of unknown kind, an opaque value -- it is a boolean the solver may
  choose, which only adds models."
  [st v]
  (cond
    (:vec v) (if-let [vk (:kind v)] (= :vector vk) (unknown! st 'vector? v :bool))
    (contains? v :opaque) (unknown! st 'vector? v :bool)
    :else false))

(defn- sequential-value? [st v]
  (cond (:vec v) true
        (contains? v :opaque) (unknown! st 'sequential? v :bool)
        :else false))

(defn- map-value? [st v]
  (cond (contains? v :opaque) (unknown! st 'map? v :bool)
        :else false))

(declare var-value)

(defn- any-value
  "A value the solver may choose freely, of any shape: what a lookup into a
  value of unknown shape returns."
  [st]
  (let [facts (atom [])
        v (var-value st facts 'Any {} 'lookup)]
    ;; its type's facts join the definitions, which the formula assumes
    (swap! st update :defs into @facts)
    v))

(defn- opaque-count
  "The count of opaque v: some count, the same each time, never negative.
  Its emptiness, and whether its seq is nil, are read off it."
  [st v]
  (or (get-in @st [:unknowns ['count v]])
      (let [c (unknown! st 'count v :int)]
        (swap! st update :defs conj [:<= 0 c])
        c)))

(defn- opaque-rest
  "The rest of opaque v: a seq, never nil and never a vector, one shorter
  than v unless v is empty.  The same value each time it is asked for."
  [st v]
  (or (get-in @st [:unknown-values ['rest v]])
      (let [r {:opaque (unknown! st 'rest v :int)}
            n (opaque-count st v)]
        (swap! st #(-> %
                       (assoc-in [:unknown-values ['rest v]] r)
                       (assoc-in [:unknowns ['sequential? r]] true)
                       (assoc-in [:unknowns ['vector? r]] false)))
        (swap! st update :defs conj [:= (opaque-count st r) [:ite [:= n 0] 0 [:- n 1]]])
        r)))

(defn- unknown-value
  "What op returns of an opaque v: some value, the same each time op is
  asked of v (Ackermann again)."
  [st op v]
  (let [k [op v]]
    (or (get-in @st [:unknown-values k])
        (let [x (any-value st)] (swap! st assoc-in [:unknown-values k] x) x))))

(def ^:private pure-fns
  '#{sort distinct reverse sort-by str name keyword subs frequencies last butlast take drop count})

(defn- nil-formula
  "The formula for 'v is nil'."
  [v]
  (cond (= :bottom v) false
        (:union v) (into [:or false] (for [[g x] (:union v)] (conj-f g (boolean (:nil x)))))
        :else (boolean (:nil v))))

(defn- core
  "A clojure.core fn applied to values."
  [st f args]
  (if-let [v (and (contains? pure-fns f)
                  ;; a throw in an argument is a throw of the call, as
                  ;; lift makes it for the fns it handles
                  (if (some #{:bottom} args)
                    :bottom
                    (let [xs (map #(concrete st %) args)]
                    (when (not-any? #{::none} xs)
                      (try (let [r (apply @(resolve (symbol "clojure.core" (name f))) xs)]
                             (from-concrete st (if (seq? r) (doall r) r)))
                           (catch Throwable _ nil))))))]
    v
    (core* st f args)))

(defn- core*
  "A clojure.core fn applied to values."
  [st f args]
  (let [[a b c] args
        n (count args)
        num (fn [g] (lift st (fn [x] {:int (g (int-of x))}) a))
        num2 (fn [g] (lift2 st (fn [x y] {:int (g (int-of x) (int-of y))}) a b))]
    (case f
      + (reduce (fn [acc x] (lift2 st (fn [p q] {:int [:+ (int-of p) (int-of q)]}) acc x)) {:int 0} args)
      - (if (= 1 n)
          (num (fn [x] [:neg x]))
          (reduce (fn [acc x] (lift2 st (fn [p q] {:int [:- (int-of p) (int-of q)]}) acc x)) a (rest args)))
      * (reduce (fn [acc x]
                  (lift2 st (fn [p q]
                              (let [s (fold (int-of p)) u (fold (int-of q))]
                                (cond (integer? s) {:int [:* s u]}
                                      (integer? u) {:int [:* u s]}
                                      :else (give-up! "a product of two unknowns"))))
                         acc x))
                {:int 1} args)
      inc (num (fn [x] [:+ x 1]))
      dec (num (fn [x] [:- x 1]))
      (quot mod rem) (lift2 st (fn [x y]
                                 (let [k (int-of y)]
                                   (when-not (and (integer? k) (not (zero? k)))
                                     (give-up! (str f " by a value that is not a literal")))
                                   {:int (case f
                                           quot [:quot (int-of x) k]
                                           mod [:mod (int-of x) k]
                                           rem [:- (int-of x) [:* k [:quot (int-of x) k]]])}))
                            a b)
      abs (num (fn [x] [:abs x]))
      bit-shift-left
      (lift2 st (fn [x k]
                  (let [xv (fold (int-of x)) kv (fold (int-of k))]
                    (cond
                      (and (integer? xv) (integer? kv) (<= 0 kv 62)) {:int (bit-shift-left xv kv)}
                      :else
                      ;; x times 2^k for each k a shift can be; anything else
                      ;; is a value the solver may choose, which proves less
                      (let [other (fresh! st :int)
                            [lo hi] (interval st kv)
                            js (range (max 0 (or lo 0)) (inc (min 62 (or hi 62))))]
                        {:int (reduce (fn [acc j] [:ite (define! st :bool [:= kv j]) [:* (bit-shift-left 1 j) xv] acc])
                                      other (reverse js))}))))
             a b)
      max (reduce (fn [acc x] (lift2 st (fn [p q] {:int [:max (int-of p) (int-of q)]}) acc x)) a (rest args))
      min (reduce (fn [acc x] (lift2 st (fn [p q] {:int [:min (int-of p) (int-of q)]}) acc x)) a (rest args))
      (< <= > >=) (if (= 1 n)
                    {:bool true}
                    {:bool (reduce conj-f true
                                   (map (fn [x y] (truth (lift2 st (fn [p q] {:bool (num-test st f [p q] #(compare-int (keyword (name f)) p q))}) x y)))
                                        args (rest args)))})
      = (if (= 1 n)
          {:bool true}
          {:bool (reduce conj-f true
                         ;; the same symbolic value is equal to itself: no
                         ;; need to split it into its alternatives
                         (map (fn [x y] (if (= x y) true (truth (lift2 st (fn [p q] {:bool (equal st p q)}) x y))))
                              args (rest args)))})
      not= {:bool [:not (truth (core st '= args))]}
      not {:bool [:not (truth a)]}
      boolean {:bool (truth a)}
      zero? (lift st (fn [x] {:bool (num-test st 'zero? [x] #(vector := (int-of x) 0))}) a)
      pos? (lift st (fn [x] {:bool (num-test st 'pos? [x] #(vector :> (int-of x) 0))}) a)
      neg? (lift st (fn [x] {:bool (num-test st 'neg? [x] #(vector :< (int-of x) 0))}) a)
      identity a
      hash-set (finite-set st (map (fn [x] [true x]) args) true)
      set (lift st (fn [x] (cond (:set x) {:set (assoc (:set x) :distinct true)}
                                 :else (finite-set st (map (fn [e] [true e]) (seq-of x)) true)))
                a)
      contains? (lift2 st (fn [sv x]
                            (cond (:set sv) {:bool ((:mem (:set sv)) x)}
                                  (:map sv) (do (named! sv x)
                                                {:bool (into [:or false] (for [[p k _] (:map sv)] (conj-f p (same-key st x k))))})
                                  (:nil sv) {:bool false}
                                  :else (give-up! "contains? on a value that is not a set or map")))
                       a b)
      into (lift2 st (fn [x y]
                       (when-not (:set x) (give-up! "into a value that is not a set"))
                       (let [sy (if (:set y) (:set y) (:set (finite-set st (map (fn [e] [true e]) (seq-of y)) false)))
                             sx (:set x)]
                         {:set {:mem (fn [e] [:or ((:mem sx) e) ((:mem sy) e)])
                                :elems (when (and (:elems sx) (:elems sy)) (into (:elems sx) (:elems sy)))
                                :distinct true
                                :elem (or (:elem sx) (:elem sy))}}))
                  a b)
      filter (lift st (fn [xs]
                        (let [keep? (fn [e] (truth (apply-fn st a [e])))
                              sx (cond (:set xs) (:set xs)
                                       ;; a seq of known length, filtered: which
                                       ;; elements stay depends on the tests,
                                       ;; and they stay in order
                                       (:vec xs) (:set (ordered st (map (fn [e] [true e]) (:vec xs))))
                                       :else (seq-of xs))]
                          {:set {:mem (fn [e] [:and ((:mem sx) e) (keep? e)])
                                 :elems (when (:elems sx) (vec (for [[g v] (:elems sx)] [(conj-f g (keep? v)) v])))
                                 :distinct (:distinct sx)
                                 :ordered (:ordered sx)
                                 :elem (:elem sx)}}))
                b)
      ;; keep over a seq of known length: f's values, each there when it is
      ;; not nil
      keep (lift st (fn [xs]
                      (cond
                        (:nil xs) {:vec [] :kind :seq}
                        (guarded-elems xs)
                        (ordered st (for [[g e] (guarded-elems xs)
                                          :let [v (apply-fn st a [e])]]
                                      [(conj-f g [:not (nil-formula v)]) v]))
                        :else (give-up! "keep over a collection of unknown size or order")))
                 b)
      (map mapcat) (lift st (fn [xs]
                              (cond
                                (:vec xs) (if (= 'map f)
                                            {:vec (mapv #(apply-fn st a [%]) (:vec xs)) :kind :seq}
                                            {:vec (vec (mapcat #(seq-of (apply-fn st a [%])) (:vec xs))) :kind :seq})
                                (:set xs) (image st f a (:set xs))
                                :else (seq-of xs)))
                         b)
      list {:vec (vec args) :kind :seq}
      vector {:vec (vec args) :kind :vector}
      vec (lift st (fn [x] {:vec (seq-of x) :kind :vector}) a)
      vector? (lift st (fn [x] {:bool (kind-is? st x)}) a)
      nil? (lift st (fn [x] {:bool (boolean (:nil x))}) a)
      (keyword? symbol? string? char?)
      (let [want ({'keyword? :keyword 'symbol? :symbol 'string? :string 'char? :char} f)]
        (lift st (fn [x]
                   {:bool (cond
                            (contains? x :const) (if-let [k (:ctype x)] (= want k) (unknown! st f x :bool))
                            ;; an opaque value is none of the constants
                            :else false)})
              a))
      boolean? (lift st (fn [x] {:bool (contains? x :bool)}) a)
      some? (lift st (fn [x] {:bool (not (:nil x))}) a)
      ;; an opaque value is none of the integers, so it is not one
      integer? (lift st (fn [x] {:bool (contains? x :int)}) a)
      ;; a fn value is one; a law's values are data, so no other is
      fn? (lift st (fn [x] {:bool (contains? x :fn)}) a)
      sequential? (lift st (fn [x] {:bool (sequential-value? st x)}) a)
      map? (lift st (fn [x] {:bool (if (:map x) true (map-value? st x))}) a)
      hash-map (reduce (fn [m [k v]] (map-assoc st m k v true)) {:map []} (partition 2 args))
      assoc (reduce (fn [m [k v]] (lift st (fn [mm] (map-assoc st (as-map mm) k v true)) m))
                    a (partition 2 (rest args)))
      dissoc (reduce (fn [m k] (lift st (fn [mm] (map-without st (as-map mm) k true)) m)) a (rest args))
      merge (if (empty? args)
              {:nil true}
              (reduce (fn [m n]
                        (lift2 st (fn [mm nn]
                                    (if (:nil nn)
                                      mm
                                      (do (open! nn "merging in the entries")
                                          (reduce (fn [acc [p k v]] (map-assoc st acc k v p))
                                                  (as-map mm) (:map (as-map nn))))))
                               m n))
                      args))
      keys (lift st (fn [x] (let [m (as-map x)]
                              (open! m "the keys")
                              (if (empty? (:map m)) {:nil true}
                                  (finite-set st (map (fn [[p k _]] [p k]) (:map m)) true))))
                 a)
      vals (lift st (fn [x] (let [m (as-map x)]
                              (open! m "the vals")
                              (if (empty? (:map m)) {:nil true}
                                  (finite-set st (map (fn [[p _ v]] [p v]) (:map m)) false))))
                 a)
      ;; distinct of a sequence of known length: each element kept unless an
      ;; earlier one equals it -- decided when the elements are, else outside
      distinct (lift st (fn [xs]
                          (cond
                            (:nil xs) {:vec [] :kind :seq}
                            (and (:vec xs) (<= (count (:vec xs)) 1)) (assoc xs :kind :seq)
                            :else (give-up! "distinct of more than one symbolic element")))
                     a)
      ;; sort-by integer keys, of a sequence of known length or the guarded
      ;; elements a filter kept: stable, so an element goes to its rank --
      ;; how many kept elements have a smaller key, or the same key and come
      ;; before it -- and place i holds the element whose rank is i
      sort-by (lift st (fn [xs]
                         (let [es (cond (:nil xs) []
                                        (guarded-elems xs) (vec (guarded-elems xs))
                                        :else (give-up! "sort-by of a collection of unknown size or order"))
                               ks (mapv (fn [[_ e]]
                                          (let [k (apply-fn st a [e])]
                                            (when (:union k) (give-up! "sort-by on a key of more than one kind"))
                                            (int-of k)))
                                        es)
                               n (count es)
                               rank (fn [j]
                                      (define! st :int
                                        (into [:+ 0]
                                              (for [k (range n) :when (not= k j)]
                                                (one-if (conj-f (first (nth es k))
                                                                (let [kk (nth ks k) kj (nth ks j)]
                                                                  (if (< k j) [:<= kk kj] [:< kk kj]))))))))
                               ranks (mapv rank (range n))
                               kept (define! st :int (into [:+ 0] (map (comp one-if first) es)))
                               place (fn [i]
                                       (reduce (fn [acc j]
                                                 (merge-values st (define! st :bool (conj-f (first (nth es j)) [:= (nth ranks j) i]))
                                                               (second (nth es j)) acc))
                                               (second (peek es)) (range (dec n) -1 -1)))]
                           (cond
                             (zero? n) {:vec [] :kind :seq}
                             (every? (comp true? first) es) {:vec (mapv place (range n)) :kind :seq}
                             :else (ordered st (map (fn [i] [(define! st :bool [:< i kept]) (place i)]) (range n))))))
                    b)
      ;; some over a seq of known length: the first element's value that is
      ;; truthy, an if for each, nil when none is
      some (lift st (fn [xs]
                      (cond
                        (:nil xs) {:nil true}
                        (guarded-elems xs) (reduce (fn [acc [g e]]
                                                     (let [v (apply-fn st a [e])]
                                                       (merge-values st (conj-f g (truth v)) v acc)))
                                                   {:nil true} (reverse (guarded-elems xs)))
                        :else (give-up! "some over a collection of unknown size")))
                 b)
      every? (lift st (fn [xs]
                        (cond
                          (:nil xs) {:bool true}
                          (:vec xs) {:bool (reduce conj-f true (map #(truth (apply-fn st a [%])) (:vec xs)))}
                          (and (:set xs) (:elems (:set xs)))
                          {:bool (reduce conj-f true (for [[g e] (:elems (:set xs))]
                                                       [:or [:not g] (truth (apply-fn st a [e]))]))}
                          :else (give-up! "every? over a collection of unknown size")))
                  b)
      reduce (if (= 3 n)
               (lift st (fn [xs]
                          (cond (:nil xs) b
                                (:vec xs) (reduce (fn [acc x] (apply-fn st a [acc x])) b (:vec xs))
                                :else (give-up! "reduce over a collection of unknown order")))
                     c)
               ;; with no initial value: the first element starts it, and
               ;; over a single element f is not called; over none, (f)
               (lift st (fn [xs]
                          (cond (:nil xs) (give-up! "reduce with no initial value over nothing")
                                (and (:vec xs) (seq (:vec xs)))
                                (reduce (fn [acc x] (apply-fn st a [acc x])) (first (:vec xs)) (rest (:vec xs)))
                                :else (give-up! "reduce with no initial value over a collection of unknown order")))
                     b))
      ;; the vector forms, as the seq forms: vector? of them is not decided
      mapv (core* st 'map args)
      filterv (core* st 'filter args)
      not-any? {:bool [:not (truth (core* st 'some args))]}
      get (if (<= 2 n 3)
            (lift2 st (fn [x i]
                        (cond
                          (:map x) (map-lookup st x i (if (= 3 n) c {:nil true}))
                          ;; get on nil, a number, a keyword or a list is nil
                          (or (:nil x) (contains? x :int) (contains? x :const) (contains? x :bool)
                              (and (:vec x) (= :seq (:kind x))))
                          (if (= 3 n) c {:nil true})
                          (and (:vec x) (= :vector (:kind x)) (contains? i :int)
                               (integer? (fold (:int i))))
                          (let [k (fold (:int i)) xs (:vec x)]
                            (if (< -1 k (count xs)) (nth xs k) (if (= 3 n) c {:nil true})))
                          ;; a map, a set, a vector at an unknown index: some value
                          :else (unknown-value st 'get [x i])))
                   a b)
            (give-up! "get with more than a default"))
      ;; of an opaque value -- a map, a longer collection -- the first
      ;; element is some value, its count some count
      first (lift st (fn [x] (if (opaque? x) (unknown-value st 'first x) (or (first (seq-of x)) {:nil true}))) a)
      ;; second is the first of the rest, next the seq of it, for a value
      ;; of unknown shape as for any
      second (lift st (fn [x] (if (opaque? x)
                                 (core* st 'first [(opaque-rest st x)])
                                 (or (second (seq-of x)) {:nil true})))
                   a)
      rest (lift st (fn [x] (if (opaque? x) (opaque-rest st x) {:vec (vec (rest (seq-of x))) :kind :seq})) a)
      next (lift st (fn [x] (if (opaque? x)
                              (core* st 'seq [(opaque-rest st x)])
                              (let [r (vec (rest (seq-of x)))] (if (seq r) {:vec r :kind :seq} {:nil true}))))
                 a)
      ;; of an opaque value, what its count says: nil when it has none, some
      ;; other truthy value when it has some
      seq (lift st (fn [x]
                     (if (opaque? x)
                       (let [none [:= (opaque-count st x) 0]]
                         (union-of st [[none {:nil true}]
                                       [[:not none] {:opaque (unknown! st 'seq x :int)}]]))
                       (if (seq (seq-of x)) {:vec (seq-of x) :kind :seq} {:nil true})))
                a)
      empty? (lift st (fn [x]
                        (cond
                          (:set x)
                          (let [es (or (:elems (:set x)) (give-up! "whether a set of unknown size is empty"))]
                            {:bool [:not (into [:or false] (map first es))]})
                          (opaque? x) {:bool [:= (opaque-count st x) 0]}
                          :else {:bool (empty? (seq-of x))}))
                   a)
      count (lift st (fn [x]
                       (cond
                         (:map x) (do (open! x "the count")
                                      {:int (into [:+ 0] (map (fn [[p _ _]] [:ite p 1 0]) (:map x)))})
                         (opaque? x) {:int (opaque-count st x)}
                         (:set x)
                         (let [{:keys [elems distinct]} (:set x)]
                           (when-not elems (give-up! "the count of a set of unknown size"))
                           {:int (into [:+ 0]
                                       (map-indexed
                                         (fn [i [g v]]
                                           [:ite (if distinct
                                                   (conj-f g [:not (member-of st (take i elems) v)])
                                                   g)
                                            1 0])
                                         elems))})
                         :else {:int (count (seq-of x))}))
                  a)
      cons (lift2 st (fn [x ys] {:vec (into [x] (seq-of ys)) :kind :seq}) a b)
      concat {:vec (vec (mapcat (fn [x] (let [v (lift st identity x)] (seq-of v))) args)) :kind :seq}
      nth (lift2 st (fn [x i]
                      (let [k (int-of i)
                            xs (seq-of x)
                            past (if (= 3 n) c :bottom)]
                        (cond
                          ;; nth of nil is nil, or the default, at any index
                          (:nil x) (if (= 3 n) c {:nil true})
                          (integer? k)
                          (cond (< -1 k (count xs)) (nth xs k)
                                (= 3 n) c
                                :else (throws!))
                          ;; an unknown index: each position, under k = j
                          :else
                          (do (when-not (= 3 n)
                                (record-throw! st [:not (into [:or false] (for [j (range (count xs))] [:= k j]))]))
                              (reduce (fn [acc j] (merge-values st (define! st :bool [:= k j]) (nth xs j) acc))
                                      past (reverse (range (count xs))))))))
                 a b)
      (give-up! (str "`" f "`")))))

(defn- folded
  "v with each integer term in it folded."
  [v]
  (cond (= :bottom v) v
        (:union v) {:union (mapv (fn [[g x]] [g (folded x)]) (:union v))}
        (contains? v :int) {:int (fold (:int v))}
        (:vec v) (assoc v :vec (mapv folded (:vec v)))
        :else v))

(def ^:private max-unfold-depth
  "How deep a recursive definition is unfolded before evaluation gives up."
  24)

(def ^:private max-unfolds
  "How many recursive calls one goal's evaluation may unfold in all."
  400)

(defn- sig
  "The shape of a value as far as recursion on it can make progress: its
  alternatives, a vector's length and elements, an integer literal."
  [v]
  (cond (= :bottom v) :bottom
        (:union v) [:union (set (map (comp sig second) (:union v)))]
        (:vec v) [:vec (mapv sig (:vec v))]
        (and (contains? v :int) (integer? (:int v))) [:int (:int v)]
        (:map v) [:map (count (:map v))]
        :else (shape v)))

(defn- opaque-in? [g] (boolean (some #{:opaque} (tree-seq coll? seq g))))

(defn- app
  "A defn of the target or the spec applied to values: its body, run on
  them.  A recursive definition is unfolded like any other -- bounded
  unrolling: exact, since each unfolding is the code's own body -- while
  the recursion stays within max-unfold-depth and the goal within
  max-unfolds calls, which is enough when a literal drives it (a pattern
  walked down to its end) and not otherwise."
  [st f vs]
  (let [d (get-in @st [:defs-of f])]
    (when (or (nil? d) (:outside d))
      (give-up! (str "the call of `" f "`")))
    (when (:recursive? d)
      (let [{:keys [depth unfolds calls] :or {depth 0 unfolds 0}} @st
            g (mapv sig vs)]
        (when (or (>= depth max-unfold-depth) (>= unfolds max-unfolds))
          (give-up! (str "the recursion of `" f "`, unfolded as far as it may be")))
        ;; a call on values of unknown shape that has the shape of a call
        ;; around it walks into more of the same: it never bottoms out
        (when (and (opaque-in? g) (some #{[f g]} calls))
          (give-up! (str "the recursion of `" f "` over a value of unknown shape")))
        (swap! st assoc :unfolds (inc unfolds))))
    (swap! st update :used (fnil conj #{}) f)
    (let [k [f vs]
          [r tau] (or (get-in @st [:memo k])
                      ;; the body on a path of its own: what it throws on is
                      ;; noted once, and at each call under the call's path
                      (let [{:keys [path throws]} @st
                            _ (swap! st assoc :path [] :throws [])
                            ;; restored however the body ends: a give-up in
                            ;; it must not leave the caller's path emptied
                            _ (when (:recursive? d)
                                (swap! st #(-> % (update :depth (fnil inc 0))
                                               (update :calls conj [f (mapv sig vs)]))))
                            [r tau] (try
                                      (let [r (ev st (zipmap (:params d) vs) (:body d))]
                                        [r (let [ts (:throws @st)] (if (seq ts) (into [:or false] ts) false))])
                                      ;; the body ran on a path of its own, so a
                                      ;; give-up found reachable there may not be
                                      ;; on the caller's path: the caller asks again
                                      (catch clojure.lang.ExceptionInfo e
                                        (throw (if (::reachable (ex-data e))
                                                 (ex-info (ex-message e) (dissoc (ex-data e) ::reachable) e)
                                                 e)))
                                      (finally
                                        (swap! st assoc :path path :throws throws)
                                        (when (:recursive? d)
                                          (swap! st #(-> % (update :depth dec) (update :calls pop))))))]
                        (swap! st assoc-in [:memo k] [r tau])
                        [r tau]))]
      (record-throw! st tau)
      r)))

(defn- apply-fn [st fv vs]
  (cond
    (:fn fv) ((:fn fv) vs)
    ;; a map is a fn of its keys
    (and (:map fv) (<= 1 (count vs) 2)) (map-lookup st fv (first vs) (if (next vs) (second vs) {:nil true}))
    :else (give-up! "applying a value that is not a fn")))

;; --- images of sets --------------------------------------------------------------

(defn- lin
  "{:c n :m {atom k}} for a linear solver term, or nil."
  [t]
  (cond
    (integer? t) {:c t :m {}}
    (symbol? t) {:c 0 :m {t 1}}
    (and (vector? t) (= :+ (first t))) (reduce (fn [a b] (when (and a b) {:c (+ (:c a) (:c b)) :m (merge-with + (:m a) (:m b))}))
                                               {:c 0 :m {}} (map lin (rest t)))
    (and (vector? t) (= :- (first t)))
    (let [[x & ys] (map lin (rest t))]
      (when (and x (every? some? ys))
        (if (empty? ys)
          {:c (- (:c x)) :m (into {} (map (fn [[k v]] [k (- v)])) (:m x))}
          (reduce (fn [a b] {:c (- (:c a) (:c b)) :m (merge-with + (:m a) (into {} (map (fn [[k v]] [k (- v)])) (:m b)))})
                  x ys))))
    (and (vector? t) (= :neg (first t))) (when-let [x (lin (second t))]
                                           {:c (- (:c x)) :m (into {} (map (fn [[k v]] [k (- v)])) (:m x))})
    (and (vector? t) (= :* (first t)) (integer? (second t)))
    (when-let [x (lin (nth t 2))]
      (let [k (second t)] {:c (* k (:c x)) :m (into {} (map (fn [[a v]] [a (* k v)])) (:m x))}))
    :else {:c 0 :m {t 1}}))

(defn- mentions? [t syms]
  (boolean (some syms (tree-seq coll? seq t))))

(defn- offset
  "Term r is e plus a term free of the element's variables es: that term,
  or nil."
  [r e es]
  (when-let [{:keys [c m]} (lin r)]
    (when (and (= 1 (get m e)) (not-any? #(mentions? % es) (keys (dissoc m e))))
      (into [:+ c] (for [[a k] (dissoc m e) :when (not (zero? k))] [:* k a])))))

(defn- rebuild
  "A value shaped like v whose parts are the terms ts, in order."
  [v ts]
  (let [ts (atom ts)
        take! (fn [] (let [t (first @ts)] (swap! ts rest) t))]
    ((fn walk [x]
       (cond (contains? x :int) {:int (take!)}
             (contains? x :const) (assoc x :const (take!))
             (:vec x) (assoc x :vec (mapv walk (:vec x)))
             :else x))
     v)))

(defn- substitute
  "Formula f with symbols replaced by terms, as m says."
  [f m]
  (cond (symbol? f) (get m f f)
        (vector? f) (mapv #(substitute % m) f)
        :else f))

(defn- image
  "The image of a set of unknown size under fn value f (map), or the
  union of f's results (mapcat).  f is run once on an element of fresh
  variables; each result must be that element plus fixed offsets, so an
  x is in the image when x minus an offset is in the set."
  [st kind fv sx]
  (if (:elems sx)
    (let [out (for [[g v] (:elems sx)
                    :let [r (apply-fn st fv [v])]
                    [h w] (if (= 'map kind) [[true r]] (or (:elems (:set r)) (map (fn [e] [true e]) (seq-of r))))]
                [(conj-f g h) w])]
      (cond-> (finite-set st out false) (:ordered sx) (assoc-in [:set :ordered] true)))
    (let [e (fresh-like st (or (:elem sx) (give-up! "the image of a set of no known elements")))
          es (set (flat e))
          ndefs (count (:defs @st))
          r (apply-fn st fv [e])
          parts (if (= 'map kind) [[true r]] (or (:elems (:set r)) (map (fn [x] [true x]) (seq-of r))))
          _ (when (not= ndefs (count (:defs @st)))
              (give-up! "an image under a fn with tests"))
          inverses (vec (for [[g w] parts]
                          (let [ws (flat w) ecs (flat e)]
                            (when-not (and ws (= (count ws) (count ecs)))
                              (give-up! "an image that is not the element moved"))
                            (let [offs (mapv #(or (offset %1 %2 es) (give-up! "an image that is not a translation"))
                                             ws ecs)]
                              [g offs]))))]
      {:set {:mem (fn [x]
                    (if-let [xs (flat x)]
                      (into [:or false]
                            (for [[g offs] inverses
                                  :let [pre (mapv (fn [xi o] [:- xi o]) xs offs)
                                        sub (zipmap (flat e) pre)
                                        back (rebuild e pre)]]
                              (conj-f (substitute g sub) ((:mem sx) back))))
                      false))
             :distinct false
             :elem e}})))

(defn ev
  "The value of term x under env, symbol -> value."
  [st env x]
  (cond
    (symbol? x) (or (get env x) (give-up! (str "the unbound `" x "`")))
    :else
    (case (head x)
      :nil {:nil true}
      :lit (lit-value st (second x))
      :sq (lift st (fn [v] (if (:vec v) (cond-> {:vec (:vec v)} (:vector (meta x)) (assoc :kind :vector)) v))
                (elems st env (second x)))
      :if (let [c (truth (ev st env (nth x 1)))
                c (if (or (boolean? c) (symbol? c)) c (define! st :bool c))]
            (cond
              ;; a test known either way: only its branch runs, as in Clojure
              (true? c) (ev st env (nth x 2))
              (false? c) (ev st env (nth x 3))
              ;; each branch is evaluated on its own path, so a throw in it
              ;; counts only when the test takes it there
              ;; a branch that gives up where the path cannot be taken is pruned
              :else (merge-values st c
                                  (on-path st c #(pruned st (fn [] (ev st env (nth x 2)))))
                                  (on-path st [:not c] #(pruned st (fn [] (ev st env (nth x 3))))))))
      :call (folded (core st (second x) (mapv #(ev st env %) (drop 2 x))))
      :app (let [[_ f & args] x] (app st f (mapv #(ev st env %) args)))
      :fn (let [[_ ps body] x]
            {:fn (fn [vs] (ev st (merge env (zipmap ps vs)) body))})
      :cfn (let [f (second x)] {:fn (fn [vs] (folded (core st f vs))) :named x})
      :dfn (let [f (second x)] {:fn (fn [vs] (app st f vs)) :named x})
      :ap (let [[_ f & args] x]
            (apply-fn st (ev st env f) (mapv #(ev st env %) args)))
      :lin (folded {:int (into [:+ (second x)] (for [[a k] (nth x 2)] [:* k (int-of (ev st env a))]))})
      :le {:bool [:<= 0 (int-of (ev st env (second x)))]}
      :ieq {:bool [:= 0 (int-of (ev st env (second x)))]}
      :bottom (do (record-throw! st true) :bottom)
      (give-up! (str "the term " (pr-str (t/show x)))))))

;; --- goals ------------------------------------------------------------------------

(defn formula
  "{:formula :decls} saying that under hyps, goal g is truthy, for every
  value of the typed variables -- and, when opts has :total, that its
  evaluation never throws; nil when some part is outside."
  [{:keys [types defs tenv total lenient]} hyps g]
  (try
    (let [st (state)
          facts (atom [])
          _ (swap! st assoc :defs-of defs)
          occurs (reduce into (t/vars g) (map t/vars hyps))
          env (into {} (for [v (sort-by str (keys types)) :when (contains? occurs v)]
                         [v (var-value st facts (get types v) tenv v)]))
          ;; a search for a counterexample may leave out a hypothesis it
          ;; cannot read -- what it finds is run on the code before it is
          ;; believed -- where a proof needs every one
          hs (if lenient
               (vec (keep #(try (truth (ev st env %))
                                (catch clojure.lang.ExceptionInfo e
                                  (if (::outside (ex-data e)) nil (throw e))))
                          hyps))
               (mapv #(truth (ev st env %)) hyps))
          ;; what the goal may assume when it prunes a branch
          _ (swap! st assoc :assumed (into (vec @facts) hs))
          ;; only what the goal throws on counts: a hypothesis that throws
          ;; is one the law does not assume
          _ (swap! st assoc :throws [])
          goal (truth (ev st env g))
          throws (into [:or false] (:throws @st))
          goal (if total [:and [:not throws] goal] goal)]
      {:formula [:=> (into [:and true] (concat @facts (:defs @st) hs)) goal]
       :decls (:decls @st)
       :used (or (:used @st) #{})
       :env env
       :codes (:codes @st)
       :throws throws})
    (catch clojure.lang.ExceptionInfo e
      (cond
        (::outside (ex-data e)) (do (when *why* (swap! *why* conj (ex-message e))) nil)
        ;; a throw outside any alternative: give the goal back
        (::throws (ex-data e)) nil
        :else (throw e)))))

(defn- pin
  "The formula saying symbolic value v is the concrete value x."
  [st v x]
  (cond
    (= :bottom v) false
    (:union v) (into [:or] (for [[g a] (:union v)] (conj-f g (pin st a x))))
    (contains? v :int) (if (integer? x) [:= (:int v) x] false)
    (contains? v :bool) (if (boolean? x) (if x (:bool v) [:not (:bool v)]) false)
    (contains? v :const) (if (const? x) [:= (:const v) (code! st x)] false)
    (:nil v) (nil? x)
    (:vec v) (if (and (sequential? x) (= (count x) (count (:vec v)))
                      (case (:kind v) :vector (vector? x) :seq (not (vector? x)) true))
               (reduce conj-f true (map #(pin st %1 %2) (:vec v) x))
               false)
    (contains? v :opaque) (if (or (integer? x) (boolean? x) (const? x) (nil? x))
                            false
                            [:= (:opaque v) (code! st [::opaque x])])
    :else false))

(defn agrees?
  "Does the formula for term g agree with running it, at the concrete
  values of its variables in env?  For testing the evaluator: with the
  variables pinned to those values, the formula must say g is truthy
  exactly when it is.  :outside when the evaluation gives up."
  [{:keys [types defs tenv]} g env]
  (try
    (let [st (state)
          facts (atom [])
          _ (swap! st assoc :defs-of defs)
          vals (into {} (for [v (sort-by str (keys types))]
                          [v (var-value st facts (get types v) tenv v)]))
          goal (truth (ev st vals g))
          actual (try (boolean (t/evaluate g env)) (catch Throwable _ ::threw))
          pins (reduce conj-f true (for [[v x] env] (pin st (get vals v) x)))
          f [:=> (into [:and true pins] (concat @facts (:defs @st)))
             (if (= ::threw actual) true [:iff goal actual])]]
      (= :valid (:result (solve/valid? f (:decls @st) {:budget 20000}))))
    (catch clojure.lang.ExceptionInfo e
      (if (::outside (ex-data e)) :outside (throw e)))))

(defn throws-agree?
  "Does the throw condition for term g agree with running it, at the
  concrete values in env?  For testing the evaluator, like agrees?."
  [{:keys [types defs tenv]} g env]
  (try
    (let [st (state)
          facts (atom [])
          _ (swap! st assoc :defs-of defs)
          vals (into {} (for [v (sort-by str (keys types))]
                          [v (var-value st facts (get types v) tenv v)]))
          _ (ev st vals g)
          throws (into [:or false] (:throws @st))
          threw (try (t/evaluate g env) false (catch Throwable _ true))
          pins (reduce conj-f true (for [[v x] env] (pin st (get vals v) x)))
          f [:=> (into [:and true pins] (concat @facts (:defs @st))) [:iff throws threw]]]
      (= :valid (:result (solve/valid? f (:decls @st) {:budget 20000}))))
    (catch clojure.lang.ExceptionInfo e
      (if (::outside (ex-data e)) :outside (throw e)))))

(def budget
  "Decisions the solver may make on a goal evaluated whole."
  20000)

(defn- decode
  "The Clojure value symbolic value v takes in the solver's model, or
  ::none when it has none there (a throw, a set with no end)."
  [v model decoded-code]
  (let [dec #(decode % model decoded-code)
        int-at (fn [t] (if (integer? t) t (solve/eval-term t model)))]
    (cond
      (= :bottom v) ::none
      (:union v) (if-let [[_ x] (first (filter #(solve/eval-formula (first %) model) (:union v)))]
                   (dec x)
                   ::none)
      (contains? v :int) (int-at (:int v))
      (contains? v :bool) (let [b (:bool v)] (if (boolean? b) b (solve/eval-formula b model)))
      (contains? v :const) (decoded-code (int-at (:const v)) (:ctype v))
      (:nil v) nil
      (:vec v) (let [xs (mapv dec (:vec v))] (if (some #{::none} xs) ::none xs))
      ;; a map: the entries present in the model; a record's keys it does
      ;; not name are none, which is one value it may take
      (contains? v :map)
      ;; an entry whose value the model leaves open -- a list the formula
      ;; never reads -- is left out, for the caller to fill and check
      (let [es (for [[p k x] (:map v)
                     :when (if (boolean? p) p (solve/eval-formula p model))]
                 [(dec k) (dec x)])]
        (if (some #(= ::none (first %)) es)
          ::none
          (into {} (remove #(= ::none (second %))) es)))
      (:set v) (let [{:keys [pred elem]} (:set v)
                     {m :map d :default} (get model pred)]
                 (if (or (nil? pred) d)
                   ::none
                   (set (for [[args in?] m :when in?]
                          (dec (rebuild elem args))))))
      :else ::none)))

(defn counterexample
  "Values of the variables for which hyps hold and goal g does not, from
  the solver's counter-model, or nil."
  [opts hyps g]
  (when-let [{:keys [formula decls env codes]} (formula (assoc opts :lenient true) hyps g)]
    (let [r (try (solve/valid? formula decls {:budget budget})
                 (catch clojure.lang.ExceptionInfo _ nil))]
      (when (= :invalid (:result r))
        (let [by-code (into {} (map (fn [[c k]] [k c])) codes)
              ;; a constant the model picked that no literal of the code is:
              ;; a value of its own kind, apart from the others
              ;; one per code, k and -k apart, and none a literal of
              ;; the code would be
              decoded-code (fn [k ctype]
                             (let [tag (str "writ%" (if (neg? k) "n" "") (abs k))]
                               (get by-code k (case ctype
                                                :string tag
                                                :symbol (symbol tag)
                                                :char (char (+ 0x4E00 (mod k 0x5000)))
                                                (keyword tag)))))
              values (into {} (for [[v sv] env] [v (decode sv (:model r) decoded-code)]))]
          (when-not (some #{::none} (vals values))
            values))))))

(defn prove
  "[certificate fns-it-unfolded] proving goal g holds under hyps, or nil."
  [opts hyps g]
  (when-let [{:keys [formula decls used]} (formula opts hyps g)]
    (let [r (try (solve/valid? formula decls {:budget budget})
                 (catch clojure.lang.ExceptionInfo _ nil))]
      (when (and *why* (not= :valid (:result r)))
        (swap! *why* conj (str "solver: " (:result r) " " (pr-str (select-keys r [:reason :model])))))
      (when (= :valid (:result r)) [(:certificate r) used]))))

(defn verify
  "Does certificate c prove goal g under hyps?"
  [opts hyps g c]
  (if-let [{:keys [formula decls used]} (formula opts hyps g)]
    (let [ok (try (solve/verify formula decls c)
                  (catch clojure.lang.ExceptionInfo _ false))]
      ;; what a replay unfolds is what the proof reads of the code
      (when (and ok (:unfolded opts)) (swap! (:unfolded opts) into used))
      ok)
    false))
