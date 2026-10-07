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
    {:amap m}          a map of unknown size, of keys of type :kt and values
                       of type :vt (see 'maps of any size' below)
    {:seqv s}          a vector of unknown length: a slice of a base array
                       and known elements after it (see 'sequences' below)
    {:view v}          the elements of a map of unknown size or of a vector
                       of unknown length, filtered and mapped
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
            [writ.kind :as kind]
            [writ.solve :as solve]))

(def ^:dynamic *why*
  "When bound to an atom, collects why evaluations gave up, for debugging."
  nil)

(defn- give-up! [why]
  (throw (ex-info (str "outside symbolic evaluation: " why) {::outside why})))

;; --- state: fresh names, definitions and constant codes -------------------------


(defn- conj-all
  "v with xs added at its end, a conj each: into would make a transient of
  the whole of v, and on jolt that copies it."
  [v xs]
  (reduce conj v xs))

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
        (:amap v) [:amap (:base (:amap v))]
        ;; a view merges only with itself, and so does a map read by lookup
        (:view v) [:view v]
        (:mmap v) [:mmap v]
        (contains? v :repeat) [:repeat v]
        (:seqv v) (let [{:keys [base off len sfx]} (:seqv v)] [:seqv base off len (count sfx)])
        (:fn v) :fn
        (contains? v :opaque) :opaque
        :else (give-up! "a value of no known shape")))

(defn- merge-key
  "What must agree for two values to merge into one: their shape, and a
  constant's kind, so that the kinds of an Any stay apart."
  [v]
  (cond (contains? v :const) [:const (:ctype v)]
        ;; a record's value and a map that holds no other keys stay apart
        (:map v) [:map (mapv second (:map v)) (:rest v)]
        :else (shape v)))

(declare merge-values)

(defn- merge-maps
  "Two maps with the same keys, merged under c entry by entry."
  [st c a b]
  (when (not= (:rest a) (:rest b)) (give-up! "two maps, one holding keys its record does not name"))
  (cond-> {:map (mapv (fn [[p k v] [q _ w]]
                        [(define! st :bool [:or [:and c p] [:and [:not c] q]]) k (merge-values st c v w)])
                      (:map a) (:map b))}
    (:rest a) (assoc :rest (:rest a))))

(declare merge-amaps)

(defn- merge-same
  "Merge two values of one shape under formula c."
  [st c a b]
  (cond
    (= a b) a
    (:map a) (merge-maps st c a b)
    (:amap a) (merge-amaps st c a b)
    (:seqv a) (let [sa (:seqv a) sb (:seqv b)]
                {:seqv (cond-> (assoc sa :sfx (mapv #(merge-values st c %1 %2) (:sfx sa) (:sfx sb)))
                         (not= (:kind sa) (:kind sb)) (dissoc :kind))})
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

(def ^:private max-prunes
  "The most branches one goal's evaluation asks the solver about."
  20)

(def ^:private max-prune-size
  "The most definitions and path conditions a branch is pruned under."
  400)

(defn- unreachable?
  "Is the path the evaluation is on impossible, under what the goal assumes
  -- its hypotheses, its variables' facts and the definitions so far?  Asked
  of the solver, with a small budget: :unsat, :sat or :unknown."
  [st]
  (let [{:keys [assumed path decls prunes]} @st
        defs (relevant-defs st (concat assumed path))]
    ;; a large formula is not asked about: the solver's budget bounds its
    ;; search, not the work of reading the formula in, and pruning only
    ;; ever buys completeness.  Nor are more than max-prunes questions
    ;; asked of one goal
    (swap! st update :prunes (fnil inc 0))
    (if (and (<= (+ (count assumed) (count defs) (count path)) max-prune-size)
             (< (or prunes 0) max-prunes))
      ;; only an :unsat prunes, and one without congruence is one with it
      (case (:result (try (solve/check (into [:and true] (concat assumed defs path)) decls {:budget 2000 :congruence false})
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
  (when (or (:map v) (:amap v) (:seqv v) (:view v)) (give-up! "a set of collections of unknown size"))
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

(declare map-equal amap-equal seq-equal view-equal)

(defn- equal
  "The formula for (= a b)."
  [st a b]
  (let [sa (shape a) sb (shape b)]
    (cond
      (and (:view a) (:view b)) (view-equal st a b)
      (or (:view a) (:view b)) (unknown! st '= [a b] :bool)
      (and (or (:seqv a) (:seqv b))
           (let [o (if (:seqv a) b a)] (or (:seqv o) (:vec o) (contains? o :opaque) (:set o))))
      (seq-equal st a b)
      (or (:seqv a) (:seqv b)) false
      (and (:amap a) (:amap b)) (amap-equal st a b)
      ;; a map of unknown size against a map of known keys, or a value of
      ;; type Any: which keys it holds is not known
      (or (and (:amap a) (or (:map b) (contains? b :opaque)))
          (and (:amap b) (or (:map a) (contains? a :opaque))))
      (give-up! "comparing a map of unknown size with another kind of map")
      (or (:amap a) (:amap b)) false
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
  "Two maps are equal when each has every entry the other has.  A record's
  value and a map that may not hold the same other keys are equal or not
  as a boolean the solver may choose: that adds models, so a formula valid
  over them holds, and where the two meet only on paths that cannot both
  be taken, it never matters."
  [st a b]
  (if (not= (:rest a) (:rest b))
    (unknown! st '= [a b] :bool)
  (let [covers (fn [m n]
                 (reduce conj-f true
                         (for [[p k v] (:map m)]
                           [:or [:not p]
                            (into [:or false]
                                  (for [[q k2 w] (:map n)
                                        :let [sk (same-key st k k2)]
                                        ;; keys that differ: their values are never compared
                                        :when (not (false? sk))]
                                    (conj-f q (conj-f sk
                                                      (if (= v w) true (truth (lift2 st (fn [x y] {:bool (equal st x y)}) v w)))))))])))]
    (conj-f (covers a b) (covers b a)))))

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

;; --- maps of any size -------------------------------------------------------------
;;
;; A map of unknown size -- a variable of type (Map K V) or (Index :k R) -- is
;; McCarthy's array read as uninterpreted fns, as SMT solvers reduce the
;; theory of arrays: its base says, for each key, whether the key is in it
;; (a predicate of the key) and what it holds there (a value of type V whose
;; every scalar part is an uninterpreted fn of the key).  What the code does
;; to it is a chain of stores on the base, newest last: [g k p v], when
;; formula g holds, key k is in the map exactly when p holds, and holds v.
;; A lookup reads the chain from its newest store down to the base, so a
;; read over a write is an if on whether the keys are equal; two maps over
;; one base are equal when they agree at every key either chain stores, since
;; everywhere else both read the base (extensionality).  All of it is
;; integer arithmetic and uninterpreted fns, the solver's own theory, so its
;; certificates are checked as any others.

(defn- uf!
  "The uninterpreted fn (kind :fn) or predicate (:pred) of n integer
  arguments standing for the part at path of the values of map base b: one
  symbol per base and path."
  [st b path kind n]
  (let [k [(:id b) path kind]]
    (or (get-in @st [:ufs k])
        (let [f (fresh! st kind)]
          (swap! st #(-> % (assoc-in [:ufs k] f) (assoc-in [:decls f] [kind n])))
          f))))

(defn- plain-type [ty]
  (cond (symbol? ty) (symbol (name ty))
        (seq? ty) (apply list (map #(if (symbol? %) (symbol (name %)) %) ty))
        :else ty))

(declare amap-of seqv-of)

(defn- template
  "The value of type ty that map base b holds at the key whose integer
  terms are args, at part path of the base's values: each scalar part an
  uninterpreted fn of args, and the facts its type gives -- a Nat at least
  0 -- among the definitions, which the formula assumes."
  [st b path ty args]
  (let [ty (plain-type ty)
        at (fn [p kind] (into [(if (= :pred kind) :papp :app) (uf! st b p kind (count args))] args))]
    (cond
      (= 'Int ty) {:int (at path :fn)}
      (= 'Nat ty) (let [x (at path :fn)] (swap! st update :defs conj [:<= 0 x]) {:int x})
      (= 'Bool ty) {:bool (at path :pred)}
      (contains? '#{Keyword String Char Symbol} ty)
      {:const (at path :fn) :ctype ('{Keyword :keyword String :string Char :char Symbol :symbol} ty)}
      (and (seq? ty) (= 'Tuple (first ty)))
      {:vec (vec (map-indexed (fn [i t] (template st b (conj path i) t args)) (rest ty))) :kind :vector}
      (and (seq? ty) (= 'Opt (first ty)) (= 2 (count ty)))
      (let [here (at (conj path :some) :pred)]
        (union-of st [[[:not here] {:nil true}] [here (template st b (conj path :val) (second ty) args)]]))
      (and (map? ty) (seq ty) (every? keyword? (keys ty)))
      {:map (vec (for [[k kt] (sort-by (comp str key) ty)
                       :let [opt? (and (seq? kt) (= 'Opt (first (plain-type kt))))]]
                   [(if opt? (at (conj path k :in) :pred) true)
                    {:const (code! st k) :ctype :keyword}
                    (template st b (conj path k) kt args)]))
       ;; the keys its record does not name, the same at the same key
       :rest (at (conj path :rest) :fn)}
      (and (seq? ty) (= 'Vec (first ty)))
      (seqv-of st {:id [(:id b) path] :args args} (second ty) :vector)
      (and (seq? ty) (= 'List (first ty))) {:opaque (at path :fn)}
      (and (seq? ty) (or (= 'Map (first ty)) (kind/index-type? ty)))
      (amap-of st {:id [(:id b) path] :args args} ty)
      :else (give-up! (str "a map of unknown size holding values of type " (pr-str ty))))))

(defn- record-field-type [r k]
  (let [r (plain-type r)] (when (map? r) (get r k))))

(defn- amap-of
  "A map of unknown size of type ty, (Map K V) or (Index :k R), over base b."
  [st b ty]
  (let [ty (plain-type ty)]
    (if (kind/index-type? ty)
      (let [{k :key r :of} (kind/index-parts ty)
            kt (or (record-field-type r k)
                   (give-up! (str "an index of records that do not name its key " k)))]
        {:amap {:base b :stores [] :kt kt :vt r :index k}})
      {:amap {:base b :stores [] :kt (nth ty 1) :vt (nth ty 2)}})))

(defn- key-terms
  "The integer terms of value x as a key of type kt, or nil when x is no
  value of kt, and so is in no map of keys of kt."
  [st x kt]
  (let [kt (plain-type kt)]
    (cond
      (contains? '#{Int Nat} kt) (when (contains? x :int) [(:int x)])
      (contains? '#{Keyword String Char Symbol} kt)
      (when (and (contains? x :const)
                 (or (nil? (:ctype x))
                     (= (:ctype x) ('{Keyword :keyword String :string Char :char Symbol :symbol} kt))))
        [(:const x)])
      (and (seq? kt) (= 'Tuple (first kt)))
      (when (and (:vec x) (= (count (:vec x)) (count (rest kt))))
        (let [ps (map #(key-terms st %1 %2) (:vec x) (rest kt))]
          (when (every? some? ps) (vec (apply concat ps)))))
      :else (give-up! (str "a map of unknown size keyed by " (pr-str kt))))))

(declare map-lookup)

(def ^:private max-gen
  "How deep instances nest: a quantified test met while instantiating
  another is one generation deeper, and only the first two are
  instantiated -- the matching depth an SMT solver bounds, so instances
  that make keys that make instances end."
  1)

(defn- base-at
  "[present value] of key x in the base of map m: whether the base holds x,
  and what, with the facts that come with reading it -- an index's record
  holds its own key, a Nat key is at least 0.  Read once per key."
  [st m x]
  (let [{:keys [base kt vt index]} (:amap m)]
    (if-let [ks (key-terms st x kt)]
      (let [k [(:id base) (:args base) ks]]
        (or (get-in @st [:base-reads k])
            (let [args (into (vec (:args base)) ks)
                  present [:papp (uf! st base [] :pred (count args)) ]
                  present (into present args)
                  v (template st base [:val] vt args)
                  facts (cond-> []
                          (= 'Nat (plain-type kt)) (conj [:=> present [:<= 0 (first ks)]])
                          index (conj [:=> present (truth (lift st (fn [r] {:bool (equal st (map-lookup st r {:const (code! st index) :ctype :keyword} {:nil true}) x)}) v))]))]
              (swap! st update :defs conj-all facts)
              (swap! st #(-> % (assoc-in [:base-reads k] [present v])
                             ;; a key the map is read at: where its quantified
                             ;; facts are instantiated, unless it was read
                             ;; deep inside another instance
                             (cond-> (<= (:gen % 0) max-gen)
                               (update-in [:ground (:id base) (:args base)] (fnil conj []) x))))
              [present v])))
      [false {:nil true}])))

(defn- amap-lookup
  "[present value] of key x in map m: the newest store at a key equal to x,
  else the base."
  [st m x]
  (reduce (fn [[pr v] [g k p w]]
            (let [c (define! st :bool (conj-f g (same-key st x k)))]
              [(define! st :bool [:or [:and c p] [:and [:not c] pr]])
               (merge-values st c w v)]))
          (base-at st m x)
          (:stores (:amap m))))

(declare apply-fn on-path pruned ev run-steps)

(defn- keyed-step
  "For a fn value (fn [acc e] (assoc acc K V)), K the entry's key and V
  reading acc only at K: a fn of the fold's init giving the step at a key
  and its value, V run with acc the init and e that entry.  nil for any
  other fn."
  [st fv]
  (let [[_ ps body] (:term fv)
        [acc e] ps
        key-of? (fn [t] (or (= t [:call 'key e]) (= t [:call 'first e])
                            (= t [:call 'nth e [:lit 0]]) (= t [:call 'nth e [:lit 0] [:nil]])))
        reads-acc-elsewhere? (fn rd [t]
                               (cond (= t acc) true
                                     (and (vector? t) (= :call (first t)) (= 'get (second t)) (= acc (nth t 2 nil))
                                          (key-of? (nth t 3 nil)))
                                     (some rd (drop 4 t))
                                     (and (vector? t) (not= :lit (first t))) (some rd (rest t))
                                     :else false))]
    (when (and (= :fn (first (:term fv))) (= 2 (count ps))
               (vector? body) (= [:call 'assoc] (subvec body 0 2)) (= 5 (count body))
               (= acc (nth body 2)) (key-of? (nth body 3))
               (not (reads-acc-elsewhere? (nth body 4))))
      (fn [init]
        (fn [x vb]
          (ev st (merge (:env fv) {acc init e {:vec [x vb] :kind :vector}}) (nth body 4)))))))

(defn- mlookup
  "[present value] of key x in a map value: a map of unknown size, one of
  known entries, nil, or maps merged or folded over (:mmap)."
  [st m x]
  (cond
    (:amap m) (amap-lookup st m x)
    (:map m) (do (named! m x)
                 [(into [:or false] (for [[p k _] (:map m)] (conj-f p (same-key st x k))))
                  (map-lookup st m x {:nil true})])
    (:nil m) [false {:nil true}]
    ;; a map's entries that pass the view's filters
    (= :entries (:op (:mmap m)))
    (let [{:keys [a steps]} (:mmap m)
          [pa va] (mlookup st a x)
          [c _] (run-steps st steps pa {:vec [x va] :kind :vector})]
      [(define! st :bool c) va])
    ;; the keys of a map, each holding x
    (= :keys-of (:op (:mmap m)))
    (let [[pa _] (mlookup st (:a (:mmap m)) x)] [pa (:x (:mmap m))])
    (:mmap m)
    (let [{:keys [op a b f step]} (:mmap m)
          [pa va] (mlookup st a x)
          [pb vb] (mlookup st b x)
          pa (define! st :bool pa)
          pb (define! st :bool pb)]
      [(define! st :bool [:or pa pb])
       (case op
         ;; the later map's value where it holds x
         :merge (merge-values st pb vb va)
         ;; both: f of the two, on the path where both hold x
         :merge-with (merge-values st pb
                                   (merge-values st pa
                                                 (on-path st [:and pa pb] #(pruned st (fn [] (apply-fn st f [va vb]))))
                                                 vb)
                                   va)
         ;; a fold that sets each key of b once: its step there, or a's
         :fold (merge-values st pb (on-path st pb #(pruned st (fn [] (step x vb)))) va))])
    :else (give-up! "a lookup in a value that is not a map")))

(defn- amap-get [st m x dflt]
  (let [[pr v] (amap-lookup st m x)]
    (merge-values st pr v dflt)))

(defn- amap-store
  "m with key k in it when p holds, holding v."
  [m k p v]
  (update-in m [:amap :stores] conj [true k p v]))

(defn- amap-equal
  "Two maps over one base are equal when they agree at every key either
  stores: everywhere else both are the base."
  [st a b]
  (if (not= (:base (:amap a)) (:base (:amap b)))
    ;; not one map changed: equal or not, as the solver chooses
    (unknown! st '= [a b] :bool)
  (let [ks (distinct (map second (concat (:stores (:amap a)) (:stores (:amap b)))))]
    (reduce conj-f true
            (for [k ks
                  :let [[pa va] (amap-lookup st a k)
                        [pb vb] (amap-lookup st b k)]]
              (conj-f [:iff pa pb]
                      [:or [:not pa] (if (= va vb) true (truth (lift2 st (fn [x y] {:bool (equal st x y)}) va vb)))]))))))

(defn- merge-amaps
  "Two maps over one base, merged under c: the stores they share, then
  each one's own under its side of c."
  [st c a b]
  (let [sa (:stores (:amap a)) sb (:stores (:amap b))
        n (count (take-while true? (map = sa sb)))
        guard (fn [g ss] (map (fn [[h k p v]] [(conj-f g h) k p v]) ss))]
    (assoc-in a [:amap :stores] (vec (concat (take n sa) (guard c (drop n sa)) (guard [:not c] (drop n sb)))))))

;; --- sequences ------------------------------------------------------------------
;;
;; A vector of unknown length -- a variable of type (Vec T), or one a map of
;; unknown size holds -- is an array too: a base, whose length is an
;; uninterpreted fn of the base's arguments and whose element at index i is
;; a value of type T built of uninterpreted fns of the arguments and i.  A
;; value is a slice of the base, [off, off+len), and the known elements the
;; code conj'd after it: first and rest move the slice, conj adds after it,
;; count is the slice's length and the known elements', and some, every?,
;; filter and the like quantify over the slice's indices as a map's over
;; its keys.

(declare witness-key run-steps)

(defn- seq-len
  "The length of sequence base b, never negative."
  [st b]
  (let [k [(:id b) (:args b) :len]]
    (or (get-in @st [:base-reads k])
        (let [args (vec (:args b))
              l (into [:app (uf! st b [:len] :fn (count args))] args)]
          (swap! st #(-> % (update :defs conj [:<= 0 l]) (assoc-in [:base-reads k] l)))
          l))))

(defn- seqv-of
  "A vector of unknown length of elements of type et over base b, whole."
  [st b et kind]
  {:seqv {:base b :off 0 :len (seq-len st b) :sfx [] :kind kind :et et}})

(defn- seq-elem
  "The element of sequence s's base at index term j."
  [st s j]
  (let [{:keys [base et]} (:seqv s)
        k [(:id base) (:args base) [:el j]]]
    (or (get-in @st [:base-reads k])
        (let [v (template st base [:el] et (conj (vec (:args base)) j))]
          (swap! st #(-> % (assoc-in [:base-reads k] v)
                         (cond-> (<= (:gen % 0) max-gen)
                           (update-in [:ground (:id base) (:args base)] (fnil conj []) {:int j}))))
          v))))

(defn- seq-slice-has
  "The formula for 'index x of s's base is in its slice'."
  [s x]
  (let [{:keys [off len]} (:seqv s)]
    (if (contains? x :int)
      [:and [:<= off (:int x)] [:< (:int x) [:+ off len]]]
      false)))

(defn- seq-count [s]
  (let [{:keys [len sfx]} (:seqv s)] (fold [:+ len (count sfx)])))

(defn- seq-nth
  "[in-range value]: s's element at index term i, counting from its start."
  [st s i]
  (let [{:keys [off len sfx]} (:seqv s)
        in-base (define! st :bool [:and [:<= 0 i] [:< i len]])
        from-sfx (reduce (fn [acc k]
                           (merge-values st (define! st :bool [:= i [:+ len k]]) (nth sfx k) acc))
                         :bottom (reverse (range (count sfx))))
        v (merge-values st in-base (seq-elem st s (fold [:+ off i])) from-sfx)]
    [(define! st :bool [:and [:<= 0 i] [:< i (seq-count s)]]) v]))

(defn- seq-first [st s]
  (let [[in v] (seq-nth st s 0)] (merge-values st in v {:nil true})))

(defn- seq-rest
  "s without its first element, a seq."
  [st s]
  (let [{:keys [off len sfx]} (:seqv s)
        ;; the test itself, not a name for it, so the rest of one slice is
        ;; the same term however often it is taken
        some? [:> len 0]]
    (if (empty? sfx)
      {:seqv (assoc (:seqv s) :off (fold [:+ off [:ite some? 1 0]]) :len (fold [:ite some? [:- len 1] 0]) :kind :seq)}
      (union-of st [[some? {:seqv (assoc (:seqv s) :off (fold [:+ off 1]) :len (fold [:- len 1]) :kind :seq)}]
                    [[:not some?] {:seqv (assoc (:seqv s) :len 0 :sfx (vec (rest sfx)) :kind :seq)}]]))))

(defn- seq-last [st s]
  (let [{:keys [off len sfx]} (:seqv s)]
    (if (seq sfx)
      (peek sfx)
      (merge-values st (define! st :bool [:> len 0]) (seq-elem st s (fold [:- [:+ off len] 1])) {:nil true}))))

(defn- seq-append
  "s with the known elements xs after it."
  [s xs]
  (update-in s [:seqv :sfx] into xs))

(defn- seq-equal
  "The formula for (= a b) where one is a vector of unknown length: the
  same slice of one base with equal known elements, or a vector of known
  length element by element; else a boolean the solver chooses."
  [st a b]
  (let [sa (:seqv a) sb (:seqv b)]
    (cond
      (and sa sb (= (:base sa) (:base sb)) (= (fold (:off sa)) (fold (:off sb)))
           (= (fold (:len sa)) (fold (:len sb))) (= (count (:sfx sa)) (count (:sfx sb))))
      (reduce conj-f true (map (fn [x y] (if (= x y) true (truth (lift2 st (fn [p q] {:bool (equal st p q)}) x y))))
                               (:sfx sa) (:sfx sb)))
      (and (or sa sb) (:vec (if sa b a)))
      (let [s (if sa a b) xs (:vec (if sa b a)) n (count xs)]
        (reduce conj-f [:= (seq-count s) n]
                (for [i (range n)]
                  (let [[_ v] (seq-nth st s i)]
                    [:or [:not [:= (seq-count s) n]]
                     (truth (lift2 st (fn [p q] {:bool (equal st p q)}) v (nth xs i)))]))))
      ;; two slices of one base: equal when as long and equal at every
      ;; index -- enough, not needed, so a boolean the solver chooses that
      ;; follows from it at a fresh index (where they differ, if anywhere),
      ;; and that says the counts agree
      (and sa sb (= (:base sa) (:base sb)) (empty? (:sfx sa)) (empty? (:sfx sb)))
      (let [r (unknown! st '= [a b] :bool)
            i (:int (witness-key st 'Int))
            same-len [:= (:len sa) (:len sb)]
            ea (seq-elem st a (fold [:+ (:off sa) i]))
            eb (seq-elem st b (fold [:+ (:off sb) i]))
            agree [:or [:not [:and [:<= 0 i] [:< i (:len sa)]]]
                   (truth (lift2 st (fn [p q] {:bool (equal st p q)}) ea eb))]]
        (swap! st update :defs conj-all [[:=> (conj-f same-len agree) r] [:=> r same-len]])
        r)
      :else (unknown! st '= [a b] :bool))))

(defn- view-equal
  "The formula for (= a b) of two views of one vector, filtered: equal when
  their filters agree at every element.  That is only enough, not needed,
  so the formula is a boolean b with b following from it: at a fresh index
  where the filters disagree, if they disagree anywhere -- the index the
  solver may choose."
  [st a b]
  (let [va (:view a) vb (:view b)]
    (if (and va vb (= (:src va) (:src vb)) (= :vals (:proj va) (:proj vb))
             (every? #(= :filter (first %)) (concat (:steps va) (:steps vb)))
             (:seqv (:src va)))
      (let [r (unknown! st '= [a b] :bool)
            src (:src va)
            i (witness-key st 'Int)
            e (seq-elem st src (:int i))
            keep (fn [steps] (first (run-steps st steps true e)))
            agree [:or [:not (seq-slice-has src i)] [:iff (keep (:steps va)) (keep (:steps vb))]]
            sfx-agree (reduce conj-f true (for [x (:sfx (:seqv src))]
                                            [:iff (first (run-steps st (:steps va) true x))
                                                  (first (run-steps st (:steps vb) true x))]))]
        (swap! st update :defs conj [:=> (conj-f agree sfx-agree) r])
        r)
      (unknown! st '= [a b] :bool))))

;; --- walking every entry of a map of unknown size ------------------------------

(declare var-value apply-fn)
;;
;; (every? f (vals m)), (some f (keys m)), (filter f (vals m)) and the like
;; quantify over the keys m holds.  The vals, keys or entries of m are a view
;; of it, a pipeline of filters and maps applied to the entry at each key;
;; a quantified test over a view is a boolean b with two sides, as an SMT
;; solver reads a quantifier:
;;
;;   - b true: the test holds at each key the formula reads the map at --
;;     the keys a lookup, a store or another quantifier's witness names --
;;     instantiated there once the goal is read (the array property fragment
;;     of Bradley, Manna and Sipma, where these instances decide it)
;;   - b false: it fails at a key w, a fresh one, the witness
;;
;; Both sides hold of b taken as the test's truth, with w its failing key
;; when there is one, so a formula valid with them is valid of the code.

(defn- view-of
  "A view of the elements of src, a map of unknown size or a vector of
  unknown length: a map's :vals, :keys or :entries, a vector's elements."
  [src proj]
  {:view {:src src :proj proj :steps []}})

(defn- view-step [v step]
  (update-in v [:view :steps] conj step))

(defn- as-view
  "x as a view: a map of unknown size as its entries, a vector of unknown
  length as its elements, a view as itself."
  [x]
  (cond (:view x) x
        (:amap x) (view-of x :entries)
        (:seqv x) (view-of x :vals)
        :else nil))

(declare seq-elem seq-slice-has)

(defn- run-steps
  "[c e] after the view's filters and maps, from element e present when c,
  at index idx of the view (a map-indexed step reads it)."
  ([st steps c e] (run-steps st steps c e nil))
  ([st steps c e idx]
   (reduce (fn [[c e] [kind f]]
             (case kind
               :filter [(conj-f c (truth (apply-fn st f [e]))) e]
               :map [c (apply-fn st f [e])]
               :map-indexed (if idx
                              [c (apply-fn st f [idx e])]
                              (give-up! "map-indexed where the index is not known"))))
           [c e] steps)))

(defn- view-at
  "[c e]: whether the view has an element at key x -- a map's key, an index
  into a vector's base -- and the element."
  [st v x]
  (let [{:keys [src proj steps]} (:view v)]
    (if (:amap src)
      (let [[pres val] (amap-lookup st src x)
            e0 (case proj :vals val :keys x :entries {:vec [x val] :kind :vector})]
        (run-steps st steps pres e0))
      (run-steps st steps (seq-slice-has src x) (seq-elem st src (:int x))
                 ;; its place in the view: from the slice's start
                 (when (contains? x :int) {:int [:- (:int x) (:off (:seqv src))]})))))

(defn- view-extra
  "[[c e] ...]: the elements a view has that no key of its base holds -- the
  known elements after a vector's slice -- after its filters and maps."
  [st v]
  (let [{:keys [src steps]} (:view v)]
    (if (:seqv src)
      (vec (map-indexed (fn [i e] (run-steps st steps true e {:int [:+ (:len (:seqv src)) i]}))
                        (:sfx (:seqv src))))
      [])))

(defn- view-base
  "The base a view's keys are keys of, and their type."
  [v]
  (let [src (:src (:view v))]
    (if (:amap src)
      [(:base (:amap src)) (:kt (:amap src))]
      [(:base (:seqv src)) 'Int])))

(defn- witness-key
  "A fresh key of type kt."
  [st kt]
  (let [facts (atom [])
        w (var-value st facts kt (:tenv @st) 'witness)]
    (swap! st update :defs conj-all @facts)
    w))

(defn- for-all!
  "The formula for 'f holds of every element of view v': a boolean with its
  failing side now, at a fresh witness key, and its holding side at each key
  the formula reads, when quantifiers are instantiated; and f at each
  element the view has that no key holds."
  [st v f]
  (let [[base kt] (view-base v)]
    ;; where a throw must be ruled out: f run at a key of its own, apart
    ;; from the witness, on the path where the view has an element there,
    ;; so what it throws on counts for every key
    (when (:total @st)
      (let [w2 (witness-key st kt)
            [c2 e2] (view-at st v w2)]
        (on-path st c2 #(guarded st (fn [e] (apply-fn st f [e])) e2))))
    (let [b (fresh! st :bool)
          w (witness-key st kt)
          [c e] (view-at st v w)
          ;; evaluated before the swap below: evaluation swaps st itself
          fails (conj-f c [:not (truth (apply-fn st f [e]))])
          extra (reduce conj-f true (for [[c e] (view-extra st v)]
                                      [:or [:not c] (truth (apply-fn st f [e]))]))]
      (swap! st #(-> %
                     (update :defs conj [:=> [:not b] fails])
                     (cond-> (< (:gen % 0) max-gen) (update-in [:ground (:id base) (:args base)] (fnil conj []) w))
                     (update :quants (fnil conj []) {:b b :view v :f f :gen (:gen % 0)})))
      (conj-f b extra))))

(defn- negated [st f]
  {:fn (fn [vs] {:bool [:not (truth (apply-fn st f vs))]}) :derived [:not f]})

(defn- exists!
  "The formula for 'f holds of some element of view v'."
  [st v f]
  [:not (for-all! st v (negated st f))])

(defn- some-in!
  "(some f v) over view v: true when f holds of some element and its
  values are booleans, or the element itself when f is a set of one; nil
  when it holds of none."
  [st v f]
  (let [ex (exists! st v f)
        one (when (and (:set f) (= 1 (count (:elems (:set f)))) (true? (ffirst (:elems (:set f)))))
              (second (first (:elems (:set f)))))]
    (cond
      (and one (or (contains? one :int) (contains? one :const)))
      (union-of st [[ex one] [[:not ex] {:nil true}]])
      ;; f at an element of no key in particular: the kind of value it gives
      (let [[_ kt] (view-base v)
            probe (apply-fn st f [(second (view-at st v (witness-key st kt)))])]
        (every? #(or (contains? (second %) :bool) (:nil (second %))) (alts probe)))
      (union-of st [[ex {:bool true}] [[:not ex] {:nil true}]])
      :else (give-up! "some over a collection of unknown size, of a fn that gives other than booleans"))))

(defn- canon
  "Term t with each fn's parameters renamed by position and depth, so two
  copies of one fn literal, #(pos? %) read twice, are one term."
  [t]
  ((fn walk [t depth]
     (cond
       (and (vector? t) (= :fn (head t)))
       (let [[_ ps body] t
             qs (mapv #(symbol (str "%" depth "_" %)) (range (count ps)))]
         [:fn qs (walk (t/subst body (zipmap ps qs)) (inc depth))])
       (and (vector? t) (not= :lit (head t))) (mapv #(walk % depth) t)
       :else t))
   t 0))

(defn- fn-sig
  "[id captured-terms] of fn value f: which fn it is -- a core or spec fn
  by name, a literal by its code, a set or a keyword used as a fn, a
  negation or composition of such -- and the integer terms of the values
  it closes over; nil when that is unknown."
  [f]
  (cond
    (:named f) [(:named f) []]
    (:term f) (let [ts (map flat (vals (:env f)))]
                (when (every? some? ts) [[(canon (:term f)) (keys (:env f))] (vec (apply concat ts))]))
    (:derived f) (let [[op & parts] (:derived f)
                       ps (map fn-sig parts)]
                   (when (every? some? ps) [(into [op] (map first ps)) (vec (mapcat second ps))]))
    (and (:set f) (:elems (:set f)) (every? (comp true? first) (:elems (:set f))))
    (let [ts (map (comp flat second) (:elems (:set f)))]
      (when (every? some? ts) [[:set (count ts)] (vec (apply concat ts))]))
    (and (contains? f :const) (= :keyword (:ctype f)) (integer? (:const f))) [[:keyword (:const f)] []]
    :else nil))

(defn- view-sig
  "[id captured-terms]: what a view's filters and maps are, as fn-sig says
  of each, or nil when one is unknown."
  [v]
  (let [parts (for [[kind f] (:steps (:view v))]
                (when-let [[id ts] (fn-sig f)] [[kind id] ts]))]
    (when (every? some? parts)
      [(mapv first parts) (vec (mapcat second parts))])))

(defn- one [c] [:ite c 1 0])

(defn- contribution
  "What element e, there when c holds, adds to an aggregate: 1 to a count,
  its value to a sum."
  [kind c e]
  (if (= :count kind) (one c) [:ite c (int-of e) 0]))

(declare witness-key)

(defn- agree!
  "Two aggregates of one kind over one base, of different fns, are equal
  when what they add agrees at a fresh key or index -- enough, since if
  they disagreed anywhere the solver could choose that place.  Noted for
  the new aggregate a against each one before it."
  [st a]
  (doseq [b (:aggs @st)
          ;; the same fn closing over other values is related by congruence
          ;; already; only different fns need agreeing
          :when (and (= (:kind a) (:kind b)) (= (:base a) (:base b))
                     (not= (first (:sig a)) (first (:sig b)))
                     (not (contains? (:agreed @st) [(first (:sig a)) (first (:sig b))])))]
    (let [w (witness-key st (:kt a))
          agree [:= ((:adds a) w) ((:adds b) w)]
          points (distinct (concat (:points a) (:points b)))
          same (if (seq points)
                 (into [:and true] (for [t points] [:= ((:at a) t) ((:at b) t)]))
                 [:= (first ((:at a) nil)) (first ((:at b) nil))])]
      (swap! st #(-> % (update :defs conj [:=> agree same])
                     (update :agreed (fnil conj #{}) [(first (:sig a)) (first (:sig b))])))))
  (swap! st update :aggs (fnil conj []) a))

(defn- view-agg
  "The count (kind :count) or the sum (:sum) of view v's elements.

  Over a map of unknown size: the aggregate over the map it was changed
  from, an uninterpreted fn of that map and of what the view's fns close
  over, plus at each key the map stores what the element there adds now
  less what it added before, each key once (a newer store at an equal key
  shadows an older one).  A count is never negative, and at least 1 where
  a key the formula reads is kept.

  Over a vector of unknown length: prefix aggregates of its base, P(0) = 0
  and P(j+1) = P(j) plus what index j adds, the latter at each index the
  formula reads; a slice is P(off+len) - P(off), and the known elements
  after it add their own."
  [st v kind]
  (let [src (:src (:view v))
        ;; a fn of unknown identity -- one closing over a map -- gets an
        ;; aggregate of its own, related to no other
        [id captured] (or (view-sig v) [[:unknown (:n (swap! st update :n inc))] []])]
    (if (:amap src)
      (let [{:keys [base stores]} (:amap src)
            base-view (assoc-in v [:view :src] (assoc-in src [:amap :stores] []))
            args (into (vec (:args base)) captured)
            cB (into [:app (uf! st base [kind id] :fn (count args))] args)
            ks (vec (distinct (map second (reverse stores))))
            add (fn [view k] (let [[c e] (view-at st view k)] (contribution kind c e)))
            deltas (for [i (range (count ks))
                         :let [k (nth ks i)
                               fresh (reduce conj-f true (for [j (range i)] [:not (same-key st k (nth ks j))]))]]
                     [:ite fresh [:- (add v k) (add base-view k)] 0])]
        (when (= :count kind)
          (swap! st #(-> % (update :defs conj [:<= 0 cB])
                         (update :counts (fnil conj []) {:c cB :view base-view}))))
        (agree! st {:kind kind :base base :sig [id captured] :at (fn [x] [cB])
                    :adds (fn [k] (add base-view k)) :kt (:kt (:amap src))})
        (fold (into [:+ cB] deltas)))
      (let [{:keys [base off len sfx]} (:seqv src)
            steps (:steps (:view v))
            args (into (vec (:args base)) captured)
            P (fn [j] (into [:app (uf! st base [:prefix kind id] :fn (inc (count args)))] (conj args j)))
            add (fn [e] (let [[c e] (run-steps st steps true e)] (contribution kind c e)))]
        (swap! st #(-> % (update :defs conj [:= (P 0) 0])
                       (update :prefixes (fnil conj []) {:base base :fact (fn [j] [:= (P [:+ j 1]) [:+ (P j) (add (seq-elem st src j))]])})
                       ;; where the slice starts: its first element's share
                       (update-in [:ground (:id base) (:args base)] (fnil conj []) {:int off})))
        (agree! st {:kind kind :base base :sig [id captured] :at P :points [off [:+ off len]]
                    :adds (fn [i] (add (seq-elem st src (:int i)))) :kt 'Int})
        (fold (into [:+ [:- (P [:+ off len]) (P off)]] (map add sfx)))))))

(defn- view-count [st v] (view-agg st v :count))

(defn- plus? [f]
  (and (:named f) (= '+ (some-> (second (:named f)) name symbol))))

(def ^:private max-instances
  "The most instances of quantified facts one goal's formula is given."
  200)

(defn- instantiate!
  "Each quantified test's holding side, at each key the formula reads its
  map at, until no key is new: an instance can read the map at another
  key, or another map.  An instance that reads what evaluation cannot is
  left out -- one fact fewer, which only weakens what is assumed."
  [st]
  (let [throws (:throws @st) path (:path @st)]
    (swap! st assoc :path [])
    (try
      (loop [round 0]
        (let [todo (for [[i q] (map-indexed vector (:quants @st))
                         :when (<= (:gen q) max-gen)
                         :let [src (:src (:view (:view q)))
                               [base] (view-base (:view q))
                               keys (distinct (concat (get-in @st [:ground (:id base) (:args base)])
                                                      (when (:amap src) (map second (:stores (:amap src))))))]
                         x keys
                         :when (not (contains? (get-in @st [:instanced i]) x))]
                     [i q x])]
          ;; a prefix aggregate's step at each index its vector is read at
          (doseq [[i {:keys [base fact]}] (map-indexed vector (:prefixes @st))
                  x (get-in @st [:ground (:id base) (:args base)])
                  :when (and (contains? x :int) (not (contains? (get-in @st [:prefixed i]) x)))]
            (swap! st update-in [:prefixed i] (fnil conj #{}) x)
            (try (let [f (fact (:int x))] (swap! st update :defs conj f))
                 (catch clojure.lang.ExceptionInfo ex
                   (when-not (or (::outside (ex-data ex)) (::throws (ex-data ex))) (throw ex)))))
          ;; a count is at least 1 where its view has an element
          (doseq [[i {:keys [c view]}] (map-indexed vector (:counts @st))
                  :let [[base] (view-base view)]
                  x (get-in @st [:ground (:id base) (:args base)])
                  :when (not (contains? (get-in @st [:counted i]) x))]
            (swap! st update-in [:counted i] (fnil conj #{}) x)
            (try (let [[in] (view-at st view x)]
                   (swap! st update :defs conj [:=> in [:<= 1 c]]))
                 (catch clojure.lang.ExceptionInfo ex
                   (when-not (or (::outside (ex-data ex)) (::throws (ex-data ex))) (throw ex)))))
          (when (and (seq todo) (< round 6) (< (:instances @st 0) max-instances))
            (doseq [[i q x] todo :while (< (:instances @st 0) max-instances)]
              (swap! st #(-> % (update-in [:instanced i] (fnil conj #{}) x) (update :instances (fnil inc 0))))
              (swap! st assoc :gen (inc (:gen q)))
              (try
                (let [[c e] (view-at st (:view q) x)
                      body (truth (apply-fn st (:f q) [e]))]
                  (swap! st update :defs conj [:=> (:b q) [:=> c body]]))
                (catch clojure.lang.ExceptionInfo ex
                  (when-not (or (::outside (ex-data ex)) (::throws (ex-data ex))) (throw ex)))
                (finally (swap! st assoc :gen 0))))
            (recur (inc round)))))
      (finally (swap! st assoc :throws throws :path path)))))

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
      (seqv-of st {:id (symbol (str "%vec" (:n (swap! st update :n inc)))) :args []} (second ty) :vector)
      ;; any seq, nil among them: opaque, so a law that only passes it
      ;; along, or a record that holds one, is decided without it; reading
      ;; it gives up
      (and (seq? ty) (= 'List (first ty)))
      {:opaque (fresh! st :int)}
      ;; a map of unknown size: a base of its own
      (and (seq? ty) (or (and (= 'Map (first ty)) (= 3 (count ty))) (kind/index-type? ty)))
      (amap-of st {:id (symbol (str "%map" (:n (swap! st update :n inc)))) :args []} ty)
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
                                 ;; known elements after a vector of unknown length
                                 (and (:seqv x) (:vec y)) (seq-append x (:vec y))
                                 (and (:vec x) (empty? (:vec x)) (:seqv y)) y
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
                              (:seqv v) v
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
        (:amap v) (give-up! "the entries of a map of unknown size")
        (or (:seqv v) (:view v)) (give-up! "every element of a vector of unknown length, in order")
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

(defn- literal-ite?
  "Is integer term t a choice among at most 16 literals: an :ite tree
  whose leaves are all integers?"
  [t]
  (letfn [(leaves [t] (cond (integer? t) 1
                            (and (vector? t) (= :ite (first t)) (= 4 (count t)))
                            (let [a (leaves (nth t 2)) b (leaves (nth t 3))]
                              (when (and a b) (+ a b)))
                            :else nil))]
    (and (vector? t) (= :ite (first t))
         (when-let [n (leaves t)] (<= n 16)))))

(defn- through-defs
  "Integer term t with each variable merging introduced replaced by its
  definition, through :ite trees up to 24 steps deep."
  ([st t] (through-defs st t 24))
  ([st t depth]
   (cond
     (zero? depth) t
     (symbol? t) (if-let [d (get-in @st [:def-of t])] (through-defs st d (dec depth)) t)
     (and (vector? t) (= :ite (first t)) (= 4 (count t)))
     [:ite (nth t 1) (through-defs st (nth t 2) (dec depth)) (through-defs st (nth t 3) (dec depth))]
     :else (fold t))))

(defn- scale-ite
  "The :ite tree t of literals with each leaf multiplied by term x."
  [t x]
  (if (integer? t) [:* t x] [:ite (nth t 1) (scale-ite (nth t 2) x) (scale-ite (nth t 3) x)]))

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
    (swap! st update :defs conj-all @facts)
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

(defn- path-of
  "The keys of a path given as a vector of known length."
  [v]
  (cond (:vec v) (:vec v)
        :else (give-up! "a path that is not a vector of known length")))

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
                                      ;; one factor is one of a few literals, as a
                                      ;; lookup in a table of rates gives: a
                                      ;; product per literal, each linear
                                      (literal-ite? (through-defs st u)) {:int (scale-ite (through-defs st u) s)}
                                      (literal-ite? (through-defs st s)) {:int (scale-ite (through-defs st s) u)}
                                      ;; two unknowns: some integer, the same for the same
                                      ;; factors -- what follows from the product being
                                      ;; one value, and nothing of multiplication
                                      :else {:int (unknown! st '* (sort-by pr-str [s u]) :int)})))
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
      ;; a remainder by 2, as integer arithmetic has it
      even? (lift st (fn [x] {:bool [:= [:mod (int-of x) 2] 0]}) a)
      odd? (lift st (fn [x] {:bool [:= [:mod (int-of x) 2] 1]}) a)
      ;; the one boolean, whatever the value's shape: a boolean is it or not,
      ;; nil and any other known shape is neither, and an opaque value
      ;; answers as some boolean, the same each time it is asked
      (true? false?)
      (lift st (fn [x]
                 (cond
                   (contains? x :bool) {:bool (if (= 'true? f) (:bool x) [:not (:bool x)])}
                   (or (:nil x) (contains? x :int) (contains? x :const) (:map x) (:vec x) (:set x)
                       (:seqv x) (:amap x))
                   {:bool false}
                   :else {:bool (unknown! st f x :bool)}))
            a)
      identity a
      hash-set (finite-set st (map (fn [x] [true x]) args) true)
      set (lift st (fn [x] (cond (:set x) {:set (assoc (:set x) :distinct true)}
                                 (as-view x)
                                 (let [v (as-view x)]
                                   {:set {:mem (fn [y] (exists! st v {:fn (fn [[e]] {:bool (equal st e y)})}))
                                          :distinct true}})
                                 :else (finite-set st (map (fn [e] [true e]) (seq-of x)) true)))
                a)
      ;; the integers from a up to b: a set by membership, its bounds kept,
      ;; so whether it is empty, its count, and its meeting with another
      ;; range are read off them
      range (if (<= 1 n 2)
              (let [[lo hi] (if (= 1 n) [{:int 0} a] [a b])]
                (lift2 st (fn [l h]
                            (let [l (int-of l) h (int-of h)]
                              {:set {:mem (fn [x] (if (contains? x :int) [:and [:<= l (int-of x)] [:< (int-of x) h]] false))
                                     :interval [l h]
                                     :distinct true}}))
                       lo hi))
              (give-up! "range with a step"))
      set-intersection (if (= 2 n)
                         (lift2 st (fn [x y]
                                     (when-not (and (:set x) (:set y)) (give-up! "intersection of values that are not sets"))
                                     (let [sx (:set x) sy (:set y)]
                                       {:set (cond-> {:mem (fn [e] [:and ((:mem sx) e) ((:mem sy) e)]) :distinct true}
                                               (and (:interval sx) (:interval sy))
                                               (assoc :interval [[:max (first (:interval sx)) (first (:interval sy))]
                                                                 [:min (second (:interval sx)) (second (:interval sy))]]))}))
                                a b)
                         (give-up! "intersection of other than two sets"))
      (set-union set-difference)
      (if (= 2 n)
        (lift2 st (fn [x y]
                    (when-not (and (:set x) (:set y)) (give-up! (str (name f) " of values that are not sets")))
                    (let [sx (:set x) sy (:set y)]
                      {:set {:mem (if (= 'set-union f)
                                    (fn [e] [:or ((:mem sx) e) ((:mem sy) e)])
                                    (fn [e] [:and ((:mem sx) e) [:not ((:mem sy) e)]]))
                             :distinct true}}))
               a b)
        (give-up! (str (name f) " of other than two sets")))
      contains? (lift2 st (fn [sv x]
                            (cond (:set sv) {:bool ((:mem (:set sv)) x)}
                                  (:amap sv) {:bool (first (amap-lookup st sv x))}
                                  (:mmap sv) {:bool (first (mlookup st sv x))}
                                  (:map sv) (do (named! sv x)
                                                {:bool (into [:or false] (for [[p k _] (:map sv)] (conj-f p (same-key st x k))))})
                                  (:nil sv) {:bool false}
                                  :else (give-up! "contains? on a value that is not a set or map")))
                       a b)
      into (lift2 st (fn [x y]
                       (when-not (or (:set x)
                                     ;; a map's entries, filtered, into an empty map
                                     (and (= [] (:map x)) (:view y) (= :entries (:proj (:view y)))
                                          (:amap (:src (:view y)))
                                          (every? #(= :filter (first %)) (:steps (:view y)))))
                         (give-up! "into a value that is not a set"))
                       (if (:map x)
                         {:mmap {:op :entries :a (:src (:view y)) :steps (:steps (:view y))}}
                         (let [sy (if (:set y) (:set y) (:set (finite-set st (map (fn [e] [true e]) (seq-of y)) false)))
                               sx (:set x)]
                           {:set {:mem (fn [e] [:or ((:mem sx) e) ((:mem sy) e)])
                                  :elems (when (and (:elems sx) (:elems sy)) (into (:elems sx) (:elems sy)))
                                  :distinct true
                                  :elem (or (:elem sx) (:elem sy))}})))
                  a b)
      filter (lift st (fn [xs]
                        (if (as-view xs)
                          (view-step (as-view xs) [:filter a])
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
                                 :elem (:elem sx)}})))
                b)
      remove (core* st 'filter [(negated st a) b])
      complement {:fn (fn [vs] {:bool [:not (truth (apply-fn st a vs))]}) :derived [:not a]}
      comp (if (empty? args)
             {:fn (fn [vs] (first vs))}
             {:fn (fn [vs] (reduce (fn [acc h] (apply-fn st h [acc]))
                                   (apply-fn st (last args) vs)
                                   (rest (reverse args))))
              :derived (into [:comp] args)})
      key (lift st (fn [e] (if (and (:vec e) (= 2 (count (:vec e)))) (first (:vec e)) (give-up! "key of a value that is not a map entry"))) a)
      val (lift st (fn [e] (if (and (:vec e) (= 2 (count (:vec e)))) (second (:vec e)) (give-up! "val of a value that is not a map entry"))) a)
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
                                (and (= 'map f) (as-view xs))
                                (view-step (as-view xs) [:map a])
                                (:vec xs) (if (= 'map f)
                                            {:vec (mapv #(apply-fn st a [%]) (:vec xs)) :kind :seq}
                                            {:vec (vec (mapcat #(seq-of (apply-fn st a [%])) (:vec xs))) :kind :seq})
                                (:set xs) (image st f a (:set xs))
                                :else (seq-of xs)))
                         b)
      ;; a fn of each element's index and the element: the index is its
      ;; place, from the slice's start, so only while no filter has
      ;; renumbered the elements, and not over a map, whose order is unknown
      map-indexed (lift st (fn [xs]
                             (cond
                               (:nil xs) {:vec [] :kind :seq}
                               (:vec xs) {:vec (vec (map-indexed (fn [i e] (apply-fn st a [{:int i} e])) (:vec xs)))
                                          :kind :seq}
                               (and (:seqv xs) (as-view xs)) (view-step (as-view xs) [:map-indexed a])
                               (and (:view xs) (:seqv (:src (:view xs)))
                                    (not-any? #(= :filter (first %)) (:steps (:view xs))))
                               (view-step xs [:map-indexed a])
                               :else (give-up! "map-indexed over a collection of unknown order")))
                       b)
      list {:vec (vec args) :kind :seq}
      vector {:vec (vec args) :kind :vector}
      vec (lift st (fn [x] (cond (:seqv x) (assoc-in x [:seqv :kind] :vector)
                                 (:view x) (assoc-in x [:view :kind] :vector)
                                 :else {:vec (seq-of x) :kind :vector})) a)
      vector? (lift st (fn [x] {:bool (cond (:seqv x) (if-let [k (:kind (:seqv x))] (= :vector k) (unknown! st 'vector? x :bool))
                                            (:view x) (if-let [k (:kind (:view x))] (= :vector k) false)
                                            :else (kind-is? st x))}) a)
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
      sequential? (lift st (fn [x] {:bool (if (or (:seqv x) (:view x)) true (sequential-value? st x))}) a)
      map? (lift st (fn [x] {:bool (cond (or (:map x) (:amap x)) true
                                         (or (:seqv x) (:view x)) false
                                         :else (map-value? st x))}) a)
      hash-map (reduce (fn [m [k v]] (map-assoc st m k v true)) {:map []} (partition 2 args))
      assoc (reduce (fn [m [k v]] (lift st (fn [mm] (if (:amap mm) (amap-store mm k true v) (map-assoc st (as-map mm) k v true))) m))
                    a (partition 2 (rest args)))
      dissoc (reduce (fn [m k] (lift st (fn [mm] (if (:amap mm) (amap-store mm k false {:nil true}) (map-without st (as-map mm) k true))) m))
                     a (rest args))
      ;; the paths of get-in, assoc-in, update-in: vectors of known length
      get-in (let [ks (path-of b)]
               (case n
                 2 (reduce (fn [m k] (core* st 'get [m k])) a ks)
                 ;; the default when any step is missing
                 3 (loop [m a, ks ks, in true]
                     (if (empty? ks)
                       (merge-values st (define! st :bool in) m c)
                       (let [k (first ks)]
                         (recur (core* st 'get [m k]) (rest ks)
                                (conj-f in (truth (lift st (fn [mm] (if (or (:map mm) (:amap mm) (:nil mm) (:set mm))
                                                                        (core* st 'contains? [mm k])
                                                                        (give-up! "get-in through a value that is not a map")))
                                                        m)))))))
                 (give-up! "get-in with more than a default")))
      assoc-in (let [ks (path-of b)]
                 (when (empty? ks) (give-up! "assoc-in with an empty path"))
                 ((fn put [m [k & more]]
                    (if (seq more)
                      (core* st 'assoc [m k (put (core* st 'get [m k]) more)])
                      (core* st 'assoc [m k c])))
                  a ks))
      update (core* st 'assoc [a b (apply-fn st c (into [(core* st 'get [a b])] (drop 3 args)))])
      update-in (let [ks (path-of b)]
                  (core* st 'assoc-in [a b (apply-fn st c (into [(core* st 'get-in [a b])] (drop 3 args)))]))
      merge (if (empty? args)
              {:nil true}
              (reduce (fn [m n]
                        (lift2 st (fn [mm nn]
                                    (cond
                                      (:nil nn) mm
                                      ;; a map of unknown size in it: merged by lookup
                                      (some #(or (:amap %) (:mmap %)) [mm nn])
                                      {:mmap {:op :merge :a mm :b nn}}
                                      :else
                                      (do (open! nn "merging in the entries")
                                          (reduce (fn [acc [p k v]] (map-assoc st acc k v p))
                                                  (as-map mm) (:map (as-map nn))))))
                               m n))
                      args))
      ;; one value over and over: only as zipmap's values
      repeat (if (= 1 n) {:repeat a} (give-up! "repeat of a count"))
      ;; (zipmap (keys m) (repeat x)): m's keys, each holding x
      zipmap (lift2 st (fn [ks vs]
                         (let [{:keys [src proj steps]} (:view ks)]
                           (if (and (:view ks) (= :keys proj) (empty? steps) (:amap src) (contains? vs :repeat))
                             {:mmap {:op :keys-of :a src :x (:repeat vs)}}
                             (give-up! "zipmap of other than a map's keys and one value"))))
                    a b)
      ;; two maps merged with f where both hold a key, read by lookup
      merge-with (if (= 3 n)
                   (lift2 st (fn [mm nn]
                               (cond (:nil nn) mm
                                     (:nil mm) nn
                                     :else {:mmap {:op :merge-with :f a :a mm :b nn}}))
                          b c)
                   (give-up! "merge-with of other than two maps"))
      keys (lift st (fn [x] (if (:amap x) (view-of x :keys) (let [m (as-map x)]
                              (open! m "the keys")
                              (if (empty? (:map m)) {:nil true}
                                  (finite-set st (map (fn [[p k _]] [p k]) (:map m)) true)))))
                 a)
      vals (lift st (fn [x] (if (:amap x) (view-of x :vals) (let [m (as-map x)]
                              (open! m "the vals")
                              (if (empty? (:map m)) {:nil true}
                                  (finite-set st (map (fn [[p _ v]] [p v]) (:map m)) false)))))
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
                        (or (:amap xs) (:seqv xs) (:view xs)) (some-in! st (as-view xs) a)
                        (guarded-elems xs) (reduce (fn [acc [g e]]
                                                     (let [v (apply-fn st a [e])]
                                                       (merge-values st (conj-f g (truth v)) v acc)))
                                                   {:nil true} (reverse (guarded-elems xs)))
                        :else (give-up! "some over a collection of unknown size")))
                 b)
      every? (lift st (fn [xs]
                        (cond
                          (:nil xs) {:bool true}
                          (or (:amap xs) (:seqv xs) (:view xs)) {:bool (for-all! st (as-view xs) a)}
                          (:vec xs) {:bool (reduce conj-f true (map #(truth (apply-fn st a [%])) (:vec xs)))}
                          (and (:set xs) (:elems (:set xs)))
                          {:bool (reduce conj-f true (for [[g e] (:elems (:set xs))]
                                                       [:or [:not g] (truth (apply-fn st a [e]))]))}
                          :else (give-up! "every? over a collection of unknown size")))
                  b)
      reduce (if (= 3 n)
               (lift st (fn [xs]
                          (cond (:nil xs) b
                                (and (plus? a) (as-view xs) (not (:vec xs)))
                                {:int [:+ (int-of b) (view-agg st (as-view xs) :sum)]}
                                (:vec xs) (reduce (fn [acc x] (apply-fn st a [acc x])) b (:vec xs))
                                ;; a step that sets the entry's own key from what
                                ;; acc holds there: a map of unknown size folded
                                ;; key by key, in any order the same
                                (and (or (:amap xs) (:mmap xs)) (keyed-step st a))
                                (lift st (fn [init] {:mmap {:op :fold :a init :b xs :step ((keyed-step st a) init)}}) b)
                                :else (give-up! "reduce over a collection of unknown order")))
                     c)
               ;; with no initial value: the first element starts it, and
               ;; over a single element f is not called; over none, (f)
               (lift st (fn [xs]
                          (cond (and (plus? a) (as-view xs)) {:int (view-agg st (as-view xs) :sum)}
                                (:nil xs) (give-up! "reduce with no initial value over nothing")
                                (and (:vec xs) (seq (:vec xs)))
                                (reduce (fn [acc x] (apply-fn st a [acc x])) (first (:vec xs)) (rest (:vec xs)))
                                :else (give-up! "reduce with no initial value over a collection of unknown order")))
                     b))
      ;; (apply + xs): the sum of xs
      apply (if (and (= 2 n) (plus? a))
              (lift st (fn [xs] (cond (as-view xs) {:int (view-agg st (as-view xs) :sum)}
                                      (:nil xs) {:int 0}
                                      :else (core* st '+ (seq-of xs))))
                    b)
              (give-up! "apply of other than + to one collection"))
      ;; the vector forms, as the seq forms: vector? of them is not decided
      mapv (core* st 'map args)
      filterv (core* st 'filter args)
      not-any? {:bool [:not (truth (core* st 'some args))]}
      get (if (<= 2 n 3)
            (lift2 st (fn [x i]
                        (cond
                          (:map x) (map-lookup st x i (if (= 3 n) c {:nil true}))
                          (:mmap x) (let [[p v] (mlookup st x i)]
                                      (merge-values st p v (if (= 3 n) c {:nil true})))
                          (:amap x) (amap-get st x i (if (= 3 n) c {:nil true}))
                          ;; a vector at an index: its element there; a seq has none
                          (:seqv x) (cond
                                      (not= :vector (:kind (:seqv x))) (if (and (= :seq (:kind (:seqv x))) true)
                                                                         (if (= 3 n) c {:nil true})
                                                                         (unknown-value st 'get [x i]))
                                      (contains? i :int) (let [[in v] (seq-nth st x (:int i))]
                                                           (merge-values st in v (if (= 3 n) c {:nil true})))
                                      :else (if (= 3 n) c {:nil true}))
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
      first (lift st (fn [x] (cond (opaque? x) (unknown-value st 'first x)
                                   (:seqv x) (seq-first st x)
                                   :else (or (first (seq-of x)) {:nil true}))) a)
      ;; second is the first of the rest, next the seq of it, for a value
      ;; of unknown shape as for any
      second (lift st (fn [x] (cond
                                (:seqv x) (core* st 'first [(seq-rest st x)])
                                (opaque? x)
                                 (core* st 'first [(opaque-rest st x)])
                                 :else
                                 (or (second (seq-of x)) {:nil true})))
                   a)
      rest (lift st (fn [x] (cond (opaque? x) (opaque-rest st x)
                                  (:seqv x) (seq-rest st x)
                                  :else {:vec (vec (rest (seq-of x))) :kind :seq})) a)
      next (lift st (fn [x] (if (or (opaque? x) (:seqv x))
                              (core* st 'seq [(if (:seqv x) (seq-rest st x) (opaque-rest st x))])
                              (let [r (vec (rest (seq-of x)))] (if (seq r) {:vec r :kind :seq} {:nil true}))))
                 a)
      ;; of an opaque value, what its count says: nil when it has none, some
      ;; other truthy value when it has some
      seq (lift st (fn [x]
                     (cond
                       (:seqv x) (let [none (define! st :bool [:= (seq-count x) 0])]
                                   (union-of st [[none {:nil true}] [[:not none] (assoc-in x [:seqv :kind] :seq)]]))
                       :else
                     (if (or (:amap x) (:view x))
                       (let [some? (exists! st (as-view x) {:fn (fn [_] {:bool true})})]
                         (union-of st [[[:not some?] {:nil true}]
                                       [some? {:opaque (unknown! st 'seq x :int)}]]))
                     (if-let [[lo hi] (:interval (:set x))]
                       (let [none [:<= hi lo]]
                         (union-of st [[none {:nil true}]
                                       [[:not none] {:opaque (unknown! st 'seq x :int)}]]))
                     (if (opaque? x)
                       (let [none [:= (opaque-count st x) 0]]
                         (union-of st [[none {:nil true}]
                                       [[:not none] {:opaque (unknown! st 'seq x :int)}]]))
                       (if (seq (seq-of x)) {:vec (seq-of x) :kind :seq} {:nil true}))))))
                a)
      empty? (lift st (fn [x]
                        (cond
                          (:seqv x) {:bool [:= (seq-count x) 0]}
                          (or (:amap x) (:view x))
                          {:bool [:not (exists! st (as-view x) {:fn (fn [_] {:bool true})})]}
                          (:interval (:set x)) (let [[lo hi] (:interval (:set x))] {:bool [:<= hi lo]})
                          (:set x)
                          (let [es (or (:elems (:set x)) (give-up! "whether a set of unknown size is empty"))]
                            {:bool [:not (into [:or false] (map first es))]})
                          (opaque? x) {:bool [:= (opaque-count st x) 0]}
                          :else {:bool (empty? (seq-of x))}))
                   a)
      count (lift st (fn [x]
                       (cond
                         (:seqv x) {:int (seq-count x)}
                         (:amap x) {:int (view-count st (view-of x :entries))}
                         (and (:view x) (:amap (:src (:view x)))) {:int (view-count st x)}
                         ;; a vector's elements, mapped: as many as it has
                         (and (:view x) (:seqv (:src (:view x)))
                              (every? #(contains? #{:map :map-indexed} (first %)) (:steps (:view x))))
                         {:int (seq-count (:src (:view x)))}
                         (and (:view x) (:seqv (:src (:view x)))) {:int (view-agg st x :count)}
                         (:map x) (do (open! x "the count")
                                      {:int (into [:+ 0] (map (fn [[p _ _]] [:ite p 1 0]) (:map x)))})
                         (opaque? x) {:int (opaque-count st x)}
                         (:interval (:set x)) (let [[lo hi] (:interval (:set x))] {:int [:max 0 [:- hi lo]]})
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
                      (cond
                        (:seqv x)
                        (let [[in v] (seq-nth st x (int-of i))]
                          (if (= 3 n)
                            (merge-values st in v c)
                            (do (record-throw! st [:not in]) (merge-values st in v :bottom))))
                        ;; a vector's elements mapped, by place or not: the step
                        ;; run on the element at that place
                        (and (:view x) (:seqv (:src (:view x)))
                             (every? #(contains? #{:map :map-indexed} (first %)) (:steps (:view x))))
                        (let [[in v0] (seq-nth st (:src (:view x)) (int-of i))
                              [_ v] (run-steps st (:steps (:view x)) true v0 {:int (int-of i)})]
                          (if (= 3 n)
                            (merge-values st in v c)
                            (do (record-throw! st [:not in]) (merge-values st in v :bottom))))
                        :else
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
                                      past (reverse (range (count xs)))))))))
                 a b)
      last (lift st (fn [x] (cond (:seqv x) (seq-last st x)
                                  (:nil x) {:nil true}
                                  :else (or (last (seq-of x)) {:nil true}))) a)
      peek (lift st (fn [x] (cond (and (:seqv x) (= :vector (:kind (:seqv x)))) (seq-last st x)
                                  (and (:vec x) (= :vector (:kind x))) (or (peek (:vec x)) {:nil true})
                                  (:nil x) {:nil true}
                                  :else (give-up! "peek of a value not known to be a vector"))) a)
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
        (:amap v) [:amap (count (:stores (:amap v)))]
        (:seqv v) [:seqv (count (:sfx (:seqv v)))]
        :else (shape v)))

(defn- opaque-in? [g] (boolean (some #{:opaque} (tree-seq coll? seq g))))

(defn- unknown-length-in?
  "Does shape g hold a vector or a map of unknown length?  A recursion on
  one walks down it as one on a value of unknown shape does."
  [g]
  (boolean (some #(and (vector? %) (contains? #{:seqv :amap} (first %))) (tree-seq coll? seq g))))

(declare app-body ev)

(defn- component-call
  "A call of a fn taken at its spec, a component's: some value of its
  return type, the same for the same arguments; it throws only where the
  arguments break its :requires, which is noted as a throw there."
  [st f vs]
  (when-let [{:keys [params term]} (get-in @st [:requires f])]
    (when-not (and term (= (count params) (count vs)))
      (give-up! (str "the :requires of `" f "`, which the prover cannot read")))
    (record-throw! st [:not (truth (ev st (zipmap params vs) term))]))
  (let [ret (get-in @st [:trusted-rets f])
        ts (map flat vs)
        base (if (every? some? ts)
               {:id [:call f] :args (vec (apply concat ts))}
               (or (get-in @st [:call-bases [f vs]])
                   (let [b {:id [:call f (:n (swap! st update :n inc))] :args []}]
                     (swap! st assoc-in [:call-bases [f vs]] b)
                     b)))]
    (template st base [:ret] ret (:args base))))

(defn- uninterpreted-call
  "The value of a call of recursive f the evaluation will not unfold: some
  value of f's return type, as Suter, Koksal and Kuncak leave a call past
  the unrolling bound uninterpreted.  Its parts are uninterpreted fns of
  the arguments' integer terms, so equal arguments give equal results;
  arguments with none give one value per distinct argument list.  Every
  value f returns is among them, so a formula valid over them holds of
  the code.  Where a throw must be ruled out, or f has no signature to
  say its type, the evaluation gives up, as why says."
  [st f vs why]
  (let [ret (get-in @st [:rets f])]
    (when (or (nil? ret) (:total @st))
      (give-up! why))
    (let [ts (map flat vs)
          base (if (every? some? ts)
                 {:id [:call f] :args (vec (apply concat ts))}
                 (or (get-in @st [:call-bases [f vs]])
                     (let [b {:id [:call f (:n (swap! st update :n inc))] :args []}]
                       (swap! st assoc-in [:call-bases [f vs]] b)
                       b)))]
      (template st base [:ret] ret (:args base)))))

(defn- app
  "A defn of the target or the spec applied to values: its body, run on
  them.  A recursive definition is unfolded like any other -- bounded
  unrolling: exact, since each unfolding is the code's own body -- while
  the recursion stays within max-unfold-depth and the goal within
  max-unfolds calls, which is enough when a literal drives it (a pattern
  walked down to its end); past that, the call's value is uninterpreted."
  [st f vs]
  (let [d (get-in @st [:defs-of f])]
    (if (and (or (nil? d) (:outside d)) (get-in @st [:trusted-rets f]))
      (component-call st f vs)
    (do
    (when (or (nil? d) (:outside d))
      (give-up! (str "the call of `" f "`")))
    (if-let [why (when (:recursive? d)
                   (let [{:keys [depth unfolds calls] :or {depth 0 unfolds 0}} @st
                         g (mapv sig vs)]
                     (cond
                       (or (>= depth max-unfold-depth) (>= unfolds max-unfolds))
                       (str "the recursion of `" f "`, unfolded as far as it may be")
                       ;; a call on values of unknown shape, or of unknown length,
                       ;; that has the shape of a call around it walks into more of
                       ;; the same: it never ends.  Unfolded on, each level's
                       ;; alternatives merge into the next, and the value grows
                       ;; past any memory before max-unfolds is reached
                       (and (or (opaque-in? g) (unknown-length-in? g)) (some #{[f g]} calls))
                       (str "the recursion of `" f "` over a value of unknown shape")
                       :else (do (swap! st assoc :unfolds (inc unfolds)) nil))))]
      (do (swap! st update :used (fnil conj #{}) f)
          (uninterpreted-call st f vs why))
      (app-body st f vs d))))))

(defn- app-body
  [st f vs d]
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
      r))

(defn- apply-fn [st fv vs]
  (cond
    (:fn fv) ((:fn fv) vs)
    ;; a map is a fn of its keys
    (and (:map fv) (<= 1 (count vs) 2)) (map-lookup st fv (first vs) (if (next vs) (second vs) {:nil true}))
    (and (:amap fv) (<= 1 (count vs) 2)) (amap-get st fv (first vs) (if (next vs) (second vs) {:nil true}))
    ;; a keyword is a fn of maps: the lookup
    (and (contains? fv :const) (= :keyword (:ctype fv)) (<= 1 (count vs) 2))
    (core* st 'get (into [(first vs) fv] (rest vs)))
    ;; a set is a fn of its elements: the element when it holds it
    (and (:set fv) (= 1 (count vs)))
    (let [in (define! st :bool ((:mem (:set fv)) (first vs)))]
      (union-of st [[in (first vs)] [[:not in] {:nil true}]]))
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
      :sq (lift st (fn [v] (cond (:vec v) (cond-> {:vec (:vec v)} (:vector (meta x)) (assoc :kind :vector))
                                 (:seqv v) (cond-> v (:vector (meta x)) (assoc-in [:seqv :kind] :vector))
                                 :else v))
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
      :call (if (= 'writ.prove.term/strict (second x))
              ;; a binding runs before the body; where nothing may throw, its
              ;; throws count whether or not the body reads it
              (do (when (:total @st) (ev st env (nth x 2)))
                  (ev st env (nth x 3)))
              (folded (core st (second x) (mapv #(ev st env %) (drop 2 x)))))
      :app (let [[_ f & args] x] (app st f (mapv #(ev st env %) args)))
      :fn (let [[_ ps body] x]
            {:fn (fn [vs] (ev st (merge env (zipmap ps vs)) body))
             ;; which fn it is: its code and the values it closes over
             :term x
             :env (into (sorted-map) (for [v (t/vars x) :when (contains? env v)] [v (get env v)]))})
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
  [{:keys [types defs tenv total lenient rets trusted-rets requires]} hyps g]
  (try
    (let [st (state)
          facts (atom [])
          _ (swap! st assoc :defs-of defs :tenv tenv :total total :rets (or rets {})
                   :trusted-rets (or trusted-rets {}) :requires (or requires {}))
          occurs (reduce into (t/vars g) (map t/vars hyps))
          env (into {} (for [v (sort-by str (keys types)) :when (contains? occurs v)]
                         [v (var-value st facts (get types v) tenv v)]))
          ;; a hypothesis it cannot read is left out.  A proof without it
          ;; holds with it -- assuming less proves more -- and what a search
          ;; for a counterexample finds is run on the code before it is
          ;; believed
          hs (vec (keep #(try (truth (ev st env %))
                              (catch clojure.lang.ExceptionInfo e
                                (if (::outside (ex-data e)) nil (throw e))))
                        hyps))
          ;; what the goal may assume when it prunes a branch
          _ (swap! st assoc :assumed (into (vec @facts) hs))
          ;; only what the goal throws on counts: a hypothesis that throws
          ;; is one the law does not assume
          _ (swap! st assoc :throws [])
          goal (truth (ev st env g))
          ;; the quantified facts, at the keys the formula reads
          _ (instantiate! st)
          throws (into [:or false] (:throws @st))
          goal (if total [:and [:not throws] goal] goal)]
      {:formula [:=> (into [:and true] (concat @facts (:defs @st) hs)) goal]
       :decls (:decls @st)
       :used (or (:used @st) #{})
       :env env
       :codes (:codes @st)
       :throws throws
       :st st})
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
          _ (swap! st assoc :defs-of defs :tenv tenv)
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
          _ (swap! st assoc :defs-of defs :tenv tenv)
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
  "Decisions the solver may make on a goal evaluated whole.  pong's
  win and play-step laws take more than 5000."
  20000)

(defn- key-of
  "[key rest-of-ints]: the value of key type kt the integers ints begin with."
  [ints kt decoded-code]
  (let [kt (plain-type kt)]
    (cond
      (contains? '#{Int Nat} kt) [(first ints) (rest ints)]
      (contains? '#{Keyword String Char Symbol} kt)
      [(decoded-code (first ints) ('{Keyword :keyword String :string Char :char Symbol :symbol} kt)) (rest ints)]
      (and (seq? kt) (= 'Tuple (first kt)))
      (reduce (fn [[out more] t] (let [[x more] (key-of more t decoded-code)] [(conj out x) more]))
              [[] ints] (rest kt))
      :else [::none ints])))

(defn- decode
  "The Clojure value symbolic value v takes in the solver's model, or
  ::none when it has none there (a throw, a set with no end).  st, the
  evaluation's state, makes the values a map of unknown size holds at the
  keys the model puts in it."
  [v model decoded-code st]
  (let [dec #(decode % model decoded-code st)
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
      ;; a map of unknown size: the keys the model's predicate holds of,
      ;; with the values the model gives there, then the stores on top
      (:amap v)
      (let [{:keys [base kt vt stores]} (:amap v)
            has (get-in @st [:ufs [(:id base) [] :pred]])
            pre (mapv int-at (:args base))
            n (count pre)
            ks (for [[args in?] (:map (get model has))
                     :when (and in? (= pre (vec (take n args))))]
                 (vec (drop n args)))
            base-map (into {} (for [ints ks
                                    :let [[k] (key-of ints kt decoded-code)
                                          x (dec (template st base [:val] vt (into pre ints)))]
                                    :when (and (not= ::none k) (not= ::none x))]
                                [k x]))]
        (reduce (fn [m [g k p w]]
                  (if (or (= ::none m) (not (if (boolean? g) g (solve/eval-formula g model))))
                    m
                    (let [kk (dec k)]
                      (cond (= ::none kk) ::none
                            (if (boolean? p) p (solve/eval-formula p model))
                            (let [x (dec w)] (if (= ::none x) (dissoc m kk) (assoc m kk x)))
                            :else (dissoc m kk)))))
                base-map stores))
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
  (when-let [{:keys [formula decls env codes st]} (formula (assoc opts :lenient true) hyps g)]
    (let [r (try (solve/valid? formula decls {:budget (or (:sym-budget opts) budget)})
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
              values (into {} (for [[v sv] env] [v (decode sv (:model r) decoded-code st)]))]
          (when-not (some #{::none} (vals values))
            values))))))

(defn- prove-under
  [opts hyps g]
  (when-let [{:keys [formula decls used]} (formula opts hyps g)]
    (let [r (try (solve/valid? formula decls {:budget (or (:sym-budget opts) budget)})
                 (catch clojure.lang.ExceptionInfo _ nil))]
      (when (and *why* (not= :valid (:result r)))
        (swap! *why* conj (str "solver: " (:result r) " " (pr-str (select-keys r [:reason :model])))))
      (when (= :valid (:result r)) [(:certificate r) used]))))

(defn- and-form?
  "Is term h an (and a b), as it is read: (if a b false), or (if a b a)
  where and's local was put back in place?"
  [h]
  (and (= :if (head h)) (or (= [:lit false] (nth h 3)) (= (nth h 1) (nth h 3)))))

(defn- guard?
  "Is hypothesis h a refinement's predicate of a law's variable, which
  opts :guards names?"
  [opts h]
  (and (= :app (head h)) (contains? (:guards opts #{}) (second h))))

(defn- without [hyps is]
  (let [is (set is)] (vec (keep-indexed (fn [i h] (when-not (contains? is i) h)) hyps))))

(declare prove*)

(defn prove
  "prove*, once per goal and hypotheses within one law's search: two
  strategies that run the same goal whole ask the solver once.  opts
  :sym-memo, an atom, holds the answers."
  [opts hyps g]
  (if-let [memo (:sym-memo opts)]
    (let [k [hyps g (:types opts) (:total opts)]]
      (if-let [e (find @memo k)]
        (val e)
        (let [r (prove* opts hyps g)] (swap! memo assoc k r) r)))
    (prove* opts hyps g)))

(defn prove*
  "[certificate fns-it-unfolded] proving goal g holds under hyps, or nil.
  Without the refinements of the law's variables first: a rule over a
  whole library is costly to read and most laws do not need it, and a
  proof under fewer hypotheses holds under all of them.  The certificate
  names the hypotheses it was made without."
  [opts hyps g]
  (let [;; (and a b), read as (if a b false), is a and b apart
        conjuncts (fn conjuncts [h]
                    (if (and-form? h)
                      (concat (conjuncts (nth h 1)) (conjuncts (nth h 2)))
                      [h]))
        ;; split only to leave guards out; otherwise the hypotheses as
        ;; they are, which a certificate without :without-hyps is replayed under
        split (if (seq (:guards opts)) (vec (mapcat conjuncts hyps)) hyps)
        gs (vec (keep-indexed (fn [i h] (when (guard? opts h) i)) split))]
    (or (when (seq gs)
          (when-let [[c used] (prove-under opts (without split gs) g)]
            [(assoc c :without-hyps gs) used]))
        (prove-under opts hyps g))))

(defn verify
  "Does certificate c prove goal g under hyps (less the ones it names as
  made without)?"
  [opts hyps g c]
  (if-let [{:keys [formula decls used]}
           (formula opts (if-let [w (:without-hyps c)]
                           (without (vec (mapcat (fn conjuncts [h]
                                                   (if (and-form? h)
                                                     (concat (conjuncts (nth h 1)) (conjuncts (nth h 2)))
                                                     [h]))
                                                 hyps))
                                    w)
                           hyps)
                    g)]
    (let [ok (try (solve/verify formula decls c)
                  (catch clojure.lang.ExceptionInfo _ false))]
      ;; what a replay unfolds is what the proof reads of the code
      (when (and ok (:unfolded opts)) (swap! (:unfolded opts) into used))
      ok)
    false))
