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
    {:const t}         a keyword, string, char or symbol, t its code
    {:nil}
    {:vec [v ...]}     a sequential value of known length
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

(defn- fresh! [st kind]
  (let [n (:n @st)
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

(defn- lit-value [st x]
  (cond
    (nil? x) {:nil true}
    (boolean? x) {:bool x}
    (integer? x) {:int x}
    (const? x) {:const (code! st x)}
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
        (:fn v) :fn
        :else (give-up! "a value of no known shape")))

(declare merge-values)

(defn- merge-same
  "Merge two values of one shape under formula c."
  [st c a b]
  (case (shape a)
    :int {:int (define! st :int [:ite c (:int a) (:int b)])}
    :const {:const (define! st :int [:ite c (:const a) (:const b)])}
    :bool {:bool (define! st :bool [:or [:and c (:bool a)] [:and [:not c] (:bool b)]])}
    :nil a
    :set (let [sa (:set a) sb (:set b)]
           {:set {:mem (fn [x] [:or [:and c ((:mem sa) x)] [:and [:not c] ((:mem sb) x)]])
                  :elems (when (and (:elems sa) (:elems sb))
                           (vec (concat (for [[g v] (:elems sa)] [(conj-f c g) v])
                                        (for [[g v] (:elems sb)] [(conj-f [:not c] g) v]))))
                  :distinct (and (:distinct sa) (:distinct sb))
                  :elem (or (:elem sa) (:elem sb))}})
    :fn (give-up! "a fn value chosen by a test")
    {:vec (mapv #(merge-values st c %1 %2) (:vec a) (:vec b))}))

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
      (let [groups (vals (group-by (comp shape second) gvs))
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
    (and (not (:union a)) (not (:union b)) (= (shape a) (shape b))) (merge-same st c a b)
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
    (union-of st (vec (for [[g x] (:union v)] [g (on-path st g #(guarded st f x))])))
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
  (if (contains? v :int) (:int v) (throws!)))

(declare equal)

(defn- fresh-like
  "A value shaped like v, of fresh variables the solver may choose."
  [st v]
  (case (shape v)
    :int {:int (fresh! st :int)}
    :const {:const (fresh! st :int)}
    :bool {:bool (fresh! st :bool)}
    :nil v
    :set (give-up! "a set of sets")
    :fn (give-up! "a set of fns")
    {:vec (mapv #(fresh-like st %) (:vec v))}))

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

(defn- equal
  "The formula for (= a b)."
  [st a b]
  (let [sa (shape a) sb (shape b)]
    (cond
      (not= sa sb) false
      (= :int sa) [:= (:int a) (:int b)]
      (= :const sa) [:= (:const a) (:const b)]
      (= :bool sa) [:iff (:bool a) (:bool b)]
      (= :nil sa) true
      (= :set sa) (let [tmpl (or (:elem (:set a)) (:elem (:set b)))]
                    (if (nil? tmpl)
                      true
                      (let [x (fresh-like st tmpl)]
                        [:iff ((:mem (:set a)) x) ((:mem (:set b)) x)])))
      (= :fn sa) (give-up! "equality of fns")
      :else (reduce conj-f true (map (fn [x y] (truth (lift2 st (fn [p q] {:bool (equal st p q)}) x y)))
                                     (:vec a) (:vec b))))))

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
      (contains? '#{Keyword String Char Symbol} ty) {:const (fresh! st :int)}
      (and (seq? ty) (= 'Tuple (first ty)))
      {:vec (mapv #(var-value st facts % tenv v) (rest ty))}
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
                          {:vec (into [{:const (code! st (keyword (str c)))}]
                                      (map #(var-value st facts % tenv v)
                                           (get-in tenv [ty :ctors c :fields])))}])
                       ctors)))
      :else (give-up! (str "a variable `" v "` of type " (pr-str ty))))))

(defn- elems
  "The values of an element list, or give up when its length is unknown."
  [st env e]
  (case (head e)
    :enil []
    :econs (into [(ev st env (nth e 1))] (elems st env (nth e 2)))
    :eapp (into (elems st env (nth e 1)) (elems st env (nth e 2)))
    :elems (let [v (ev st env (second e))]
             (cond (:vec v) (:vec v)
                   (:nil v) []
                   :else (give-up! "the elements of a value of unknown length")))
    (give-up! "an element list of unknown length")))

(defn- seq-of
  "The elements of a seqable value, as a vector of values; nil has none,
  and a number, keyword or boolean is not seqable, so Clojure throws."
  [v]
  (cond (:vec v) (:vec v)
        (:nil v) []
        (:set v) (give-up! "the order of a set's elements")
        (:fn v) (throws!)
        :else (throws!)))

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
         (and (contains? v :int) (integer? (:int v))) (:int v)
         (and (contains? v :bool) (boolean? (:bool v))) (:bool v)
         (and (contains? v :const) (contains? by-code (:const v))) (by-code (:const v))
         (:nil v) nil
         (:vec v) (let [xs (mapv walk (:vec v))] (if (some #{::none} xs) ::none (apply list xs)))
         (and (:set v) (:elems (:set v)) (every? (comp true? first) (:elems (:set v))))
         (let [xs (mapv (comp walk second) (:elems (:set v)))] (if (some #{::none} xs) ::none (set xs)))
         :else ::none))
     v)))

(defn- from-concrete
  "The symbolic value of a plain Clojure value, or nil."
  [st x]
  (cond (sequential? x) (let [vs (map #(from-concrete st %) x)] (when (every? some? vs) {:vec (vec vs)}))
        (set? x) (let [vs (map #(from-concrete st %) x)]
                   (when (every? some? vs) (finite-set st (map (fn [v] [true v]) vs) true)))
        (or (map? x) (fn? x)) nil
        :else (try (lit-value st x) (catch clojure.lang.ExceptionInfo _ nil))))

(def ^:private pure-fns
  '#{sort distinct reverse sort-by str name keyword subs frequencies last butlast take drop count})

(defn- core
  "A clojure.core fn applied to values."
  [st f args]
  (if-let [v (and (contains? pure-fns f)
                  (let [xs (map #(concrete st %) args)]
                    (when (not-any? #{::none} xs)
                      (try (let [r (apply @(resolve (symbol "clojure.core" (name f))) xs)]
                             (from-concrete st (if (seq? r) (doall r) r)))
                           (catch Throwable _ nil)))))]
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
                                   (map (fn [x y] (truth (lift2 st (fn [p q] {:bool (compare-int (keyword (name f)) p q)}) x y)))
                                        args (rest args)))})
      = (if (= 1 n)
          {:bool true}
          {:bool (reduce conj-f true
                         (map (fn [x y] (truth (lift2 st (fn [p q] {:bool (equal st p q)}) x y)))
                              args (rest args)))})
      not= {:bool [:not (truth (core st '= args))]}
      not {:bool [:not (truth a)]}
      boolean {:bool (truth a)}
      zero? (lift st (fn [x] {:bool [:= (int-of x) 0]}) a)
      pos? (lift st (fn [x] {:bool [:> (int-of x) 0]}) a)
      neg? (lift st (fn [x] {:bool [:< (int-of x) 0]}) a)
      identity a
      hash-set (finite-set st (map (fn [x] [true x]) args) true)
      set (lift st (fn [x] (cond (:set x) {:set (assoc (:set x) :distinct true)}
                                 :else (finite-set st (map (fn [e] [true e]) (seq-of x)) true)))
                a)
      contains? (lift2 st (fn [sv x]
                            (if (:set sv) {:bool ((:mem (:set sv)) x)} (give-up! "contains? on a value that is not a set")))
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
                                       ;; elements stay depends on the tests
                                       (:vec xs) (:set (finite-set st (map (fn [e] [true e]) (:vec xs)) false))
                                       :else (seq-of xs))]
                          {:set {:mem (fn [e] [:and ((:mem sx) e) (keep? e)])
                                 :elems (when (:elems sx) (vec (for [[g v] (:elems sx)] [(conj-f g (keep? v)) v])))
                                 :distinct (:distinct sx)
                                 :elem (:elem sx)}}))
                b)
      (map mapcat) (lift st (fn [xs]
                              (cond
                                (:vec xs) (if (= 'map f)
                                            {:vec (mapv #(apply-fn st a [%]) (:vec xs))}
                                            {:vec (vec (mapcat #(seq-of (apply-fn st a [%])) (:vec xs)))})
                                (:set xs) (image st f a (:set xs))
                                :else (seq-of xs)))
                         b)
      (list vector) {:vec (vec args)}
      vec (lift st (fn [x] {:vec (seq-of x)}) a)
      first (lift st (fn [x] (or (first (seq-of x)) {:nil true})) a)
      second (lift st (fn [x] (or (second (seq-of x)) {:nil true})) a)
      rest (lift st (fn [x] {:vec (vec (rest (seq-of x)))}) a)
      next (lift st (fn [x] (let [r (vec (rest (seq-of x)))] (if (seq r) {:vec r} {:nil true}))) a)
      seq (lift st (fn [x] (if (seq (seq-of x)) {:vec (seq-of x)} {:nil true})) a)
      empty? (lift st (fn [x]
                        (if (:set x)
                          (let [es (or (:elems (:set x)) (give-up! "whether a set of unknown size is empty"))]
                            {:bool [:not (into [:or false] (map first es))]})
                          {:bool (empty? (seq-of x))}))
                   a)
      count (lift st (fn [x]
                       (if (:set x)
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
                         {:int (count (seq-of x))}))
                  a)
      cons (lift2 st (fn [x ys] {:vec (into [x] (seq-of ys))}) a b)
      concat {:vec (vec (mapcat (fn [x] (let [v (lift st identity x)] (seq-of v))) args))}
      nth (lift2 st (fn [x i]
                      (let [k (int-of i)
                            xs (seq-of x)
                            past (if (= 3 n) c :bottom)]
                        (if (integer? k)
                          (cond (< -1 k (count xs)) (nth xs k)
                                (= 3 n) c
                                :else (throws!))
                          ;; an unknown index: each position, under k = j
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
        (:vec v) {:vec (mapv folded (:vec v))}
        :else v))

(defn- app
  "A defn of the target or the spec applied to values: its body, run on
  them.  Recursion is outside."
  [st f vs]
  (let [d (get-in @st [:defs-of f])]
    (when (or (nil? d) (:recursive? d) (:outside d))
      (give-up! (str "the call of `" f "`")))
    (swap! st update :used (fnil conj #{}) f)
    (let [k [f vs]
          [r tau] (or (get-in @st [:memo k])
                      ;; the body on a path of its own: what it throws on is
                      ;; noted once, and at each call under the call's path
                      (let [{:keys [path throws]} @st
                            _ (swap! st assoc :path [] :throws [])
                            r (ev st (zipmap (:params d) vs) (:body d))
                            tau (let [ts (:throws @st)] (if (seq ts) (into [:or false] ts) false))]
                        (swap! st assoc :path path :throws throws)
                        (swap! st assoc-in [:memo k] [r tau])
                        [r tau]))]
      (record-throw! st tau)
      r)))

(defn- apply-fn [st fv vs]
  (if (:fn fv)
    ((:fn fv) vs)
    (give-up! "applying a value that is not a fn")))

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
             (contains? x :const) {:const (take!)}
             (:vec x) {:vec (mapv walk (:vec x))}
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
      (finite-set st out false))
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
      :sq {:vec (elems st env (second x))}
      :if (let [c (truth (ev st env (nth x 1)))
                c (if (or (boolean? c) (symbol? c)) c (define! st :bool c))]
            (cond
              ;; a test known either way: only its branch runs, as in Clojure
              (true? c) (ev st env (nth x 2))
              (false? c) (ev st env (nth x 3))
              ;; each branch is evaluated on its own path, so a throw in it
              ;; counts only when the test takes it there
              :else (merge-values st c
                                  (on-path st c #(ev st env (nth x 2)))
                                  (on-path st [:not c] #(ev st env (nth x 3))))))
      :call (folded (core st (second x) (mapv #(ev st env %) (drop 2 x))))
      :app (let [[_ f & args] x] (app st f (mapv #(ev st env %) args)))
      :fn (let [[_ ps body] x]
            {:fn (fn [vs] (ev st (merge env (zipmap ps vs)) body))})
      :cfn (let [f (second x)] {:fn (fn [vs] (folded (core st f vs)))})
      :dfn (let [f (second x)] {:fn (fn [vs] (app st f vs))})
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
  [{:keys [types defs tenv total]} hyps g]
  (try
    (let [st (state)
          facts (atom [])
          _ (swap! st assoc :defs-of defs)
          occurs (reduce into (t/vars g) (map t/vars hyps))
          env (into {} (for [v (sort-by str (keys types)) :when (contains? occurs v)]
                         [v (var-value st facts (get types v) tenv v)]))
          hs (mapv #(truth (ev st env %)) hyps)
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
    (:vec v) (if (and (sequential? x) (= (count x) (count (:vec v))))
               (reduce conj-f true (map #(pin st %1 %2) (:vec v) x))
               false)
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
      (contains? v :const) (decoded-code (int-at (:const v)))
      (:nil v) nil
      (:vec v) (let [xs (mapv dec (:vec v))] (if (some #{::none} xs) ::none xs))
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
  (when-let [{:keys [formula decls env codes]} (formula opts hyps g)]
    (let [r (try (solve/valid? formula decls {:budget budget})
                 (catch clojure.lang.ExceptionInfo _ nil))]
      (when (= :invalid (:result r))
        (let [by-code (into {} (map (fn [[c k]] [k c])) codes)
              decoded-code (fn [k] (get by-code k (keyword (str "k" (abs k)))))
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
  (if-let [{:keys [formula decls]} (formula opts hyps g)]
    (try (solve/verify formula decls c)
         (catch clojure.lang.ExceptionInfo _ false))
    false))
