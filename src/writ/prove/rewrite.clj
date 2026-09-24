(ns writ.prove.rewrite
  "Rewriting terms to normal form.

  Every rule is an equation about clojure.core that holds whenever its
  left side returns a value: rewriting never changes what a term that
  returns evaluates to.  That is Typed Clojure's notion of soundness
  (well-typed code returns a value of its type, or throws), and writ's
  law checking catches the throwing cases by running every proved law.

  Structural rules are pattern -> template pairs matched by core.logic
  unification.  The rest are computed: literals, equality, and integer
  arithmetic, which is kept in a linear normal form so that + is
  associative and commutative only where it truly is -- on integers,
  never on floats.  `self-test` checks every pattern rule against the
  runtime with test.check."
  (:require [clojure.core.logic :as l]
            [clojure.string :as str]
            [clojure.test.check :as tc]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [writ.prove.term :as t :refer [head]]))

;; --- structural rules --------------------------------------------------------
;; ?E ?A ?B ?C are element lists, ?f a fn value, any other ?x a value.

(def pattern-rules
  '[;; seq: the bridge between nil and a collection
    [seq-nil       [:call seq [:nil]]                   [:nil]]
    [seq-empty     [:call seq [:sq [:enil]]]            [:nil]]
    [seq-cons      [:call seq [:sq [:econs ?h ?E]]]     [:sq [:econs ?h ?E]]]
    [seq-elems     [:call seq [:sq [:elems ?v]]]        [:call seq ?v]]
    ;; first is nil on an empty seqable, the head otherwise
    [first-nil     [:call first [:nil]]                 [:nil]]
    [first-empty   [:call first [:sq [:enil]]]          [:nil]]
    [first-cons    [:call first [:sq [:econs ?h ?E]]]   ?h]
    [first-elems   [:call first [:sq [:elems ?v]]]      [:call first ?v]]
    ;; rest is never nil
    [rest-nil      [:call rest [:nil]]                  [:sq [:enil]]]
    [rest-empty    [:call rest [:sq [:enil]]]           [:sq [:enil]]]
    [rest-cons     [:call rest [:sq [:econs ?h ?E]]]    [:sq ?E]]
    [rest-elems    [:call rest [:sq [:elems ?v]]]       [:call rest ?v]]
    ;; next is seq of rest; empty? is not seq; second is first of rest
    [next-def      [:call next ?x]                      [:call seq [:call rest ?x]]]
    [empty-def     [:call empty? ?x]                    [:call not [:call seq ?x]]]
    [second-def    [:call second ?x]                    [:call first [:call rest ?x]]]
    ;; count
    [count-nil     [:call count [:nil]]                 [:lit 0]]
    [count-empty   [:call count [:sq [:enil]]]          [:lit 0]]
    [count-cons    [:call count [:sq [:econs ?h ?E]]]   [:call + [:lit 1] [:call count [:sq ?E]]]]
    [count-app     [:call count [:sq [:eapp ?A ?B]]]    [:call + [:call count [:sq ?A]] [:call count [:sq ?B]]]]
    [count-elems   [:call count [:sq [:elems ?v]]]      [:call count ?v]]
    ;; cons onto a seqable
    [cons-def      [:call cons ?x ?v]                   [:sq [:econs ?x [:elems ?v]]]]
    ;; element lists
    [elems-nil     [:elems [:nil]]                      [:enil]]
    [elems-sq      [:elems [:sq ?E]]                    ?E]
    [app-nil       [:eapp [:enil] ?B]                   ?B]
    [app-cons      [:eapp [:econs ?h ?A] ?B]            [:econs ?h [:eapp ?A ?B]]]
    [app-nil-r     [:eapp ?A [:enil]]                   ?A]
    [app-assoc     [:eapp [:eapp ?A ?B] ?C]             [:eapp ?A [:eapp ?B ?C]]]
    ;; not
    [not-nil       [:call not [:nil]]                   [:lit true]]
    [not-sq        [:call not [:sq ?E]]                 [:lit false]]
    [not-fn        [:call not [:fn ?p ?b]]              [:lit false]]
    ;; filter and map
    [filter-nil    [:call filter ?f [:nil]]             [:sq [:enil]]]
    [filter-empty  [:call filter ?f [:sq [:enil]]]      [:sq [:enil]]]
    [filter-cons   [:call filter ?f [:sq [:econs ?h ?E]]]
                   [:if [:ap ?f ?h]
                        [:sq [:econs ?h [:elems [:call filter ?f [:sq ?E]]]]]
                        [:call filter ?f [:sq ?E]]]]
    [filter-elems  [:call filter ?f [:sq [:elems ?v]]]  [:call filter ?f ?v]]
    [filter-app    [:call filter ?f [:sq [:eapp ?A ?B]]]
                   [:sq [:eapp [:elems [:call filter ?f [:sq ?A]]] [:elems [:call filter ?f [:sq ?B]]]]]]
    [map-nil       [:call map ?f [:nil]]                [:sq [:enil]]]
    [map-empty     [:call map ?f [:sq [:enil]]]         [:sq [:enil]]]
    [map-cons      [:call map ?f [:sq [:econs ?h ?E]]]
                   [:sq [:econs [:ap ?f ?h] [:elems [:call map ?f [:sq ?E]]]]]]
    [map-elems     [:call map ?f [:sq [:elems ?v]]]     [:call map ?f ?v]]
    ;; apply of a comparison walks the list pairwise; it needs one argument
    [apply-le-nil     [:call apply [:cfn <=] [:nil]]              [:bottom]]
    [apply-le-empty   [:call apply [:cfn <=] [:sq [:enil]]]       [:bottom]]
    [apply-le-one     [:call apply [:cfn <=] [:sq [:econs ?a [:enil]]]] [:lit true]]
    [apply-le-more    [:call apply [:cfn <=] [:sq [:econs ?a [:econs ?b ?E]]]]
                       [:if [:call <= ?a ?b] [:call apply [:cfn <=] [:sq [:econs ?b ?E]]] [:lit false]]]
    [apply-le-elems   [:call apply [:cfn <=] [:sq [:elems ?v]]]   [:call apply [:cfn <=] ?v]]
    [apply-lt-nil     [:call apply [:cfn <] [:nil]]              [:bottom]]
    [apply-lt-empty   [:call apply [:cfn <] [:sq [:enil]]]       [:bottom]]
    [apply-lt-one     [:call apply [:cfn <] [:sq [:econs ?a [:enil]]]] [:lit true]]
    [apply-lt-more    [:call apply [:cfn <] [:sq [:econs ?a [:econs ?b ?E]]]]
                       [:if [:call < ?a ?b] [:call apply [:cfn <] [:sq [:econs ?b ?E]]] [:lit false]]]
    [apply-lt-elems   [:call apply [:cfn <] [:sq [:elems ?v]]]   [:call apply [:cfn <] ?v]]
    [apply-ge-nil     [:call apply [:cfn >=] [:nil]]              [:bottom]]
    [apply-ge-empty   [:call apply [:cfn >=] [:sq [:enil]]]       [:bottom]]
    [apply-ge-one     [:call apply [:cfn >=] [:sq [:econs ?a [:enil]]]] [:lit true]]
    [apply-ge-more    [:call apply [:cfn >=] [:sq [:econs ?a [:econs ?b ?E]]]]
                       [:if [:call >= ?a ?b] [:call apply [:cfn >=] [:sq [:econs ?b ?E]]] [:lit false]]]
    [apply-ge-elems   [:call apply [:cfn >=] [:sq [:elems ?v]]]   [:call apply [:cfn >=] ?v]]
    [apply-gt-nil     [:call apply [:cfn >] [:nil]]              [:bottom]]
    [apply-gt-empty   [:call apply [:cfn >] [:sq [:enil]]]       [:bottom]]
    [apply-gt-one     [:call apply [:cfn >] [:sq [:econs ?a [:enil]]]] [:lit true]]
    [apply-gt-more    [:call apply [:cfn >] [:sq [:econs ?a [:econs ?b ?E]]]]
                       [:if [:call > ?a ?b] [:call apply [:cfn >] [:sq [:econs ?b ?E]]] [:lit false]]]
    [apply-gt-elems   [:call apply [:cfn >] [:sq [:elems ?v]]]   [:call apply [:cfn >] ?v]]
    ;; not=, max, min and abs, as the comparisons clojure.core makes
    [not=-def      [:call not= ?x ?y]                   [:call not [:call = ?x ?y]]]
    [boolean-def   [:call boolean ?x]                   [:if ?x [:lit true] [:lit false]]]
    [max-def       [:call max ?a ?b]                    [:if [:call > ?a ?b] ?a ?b]]
    [min-def       [:call min ?a ?b]                    [:if [:call < ?a ?b] ?a ?b]]
    [abs-def       [:call abs ?a]                       [:if [:call neg? ?a] [:call - ?a] ?a]]
    ;; a comparison of three is two, the second only if the first holds
    [le3           [:call <= ?a ?b ?c]                  [:if [:call <= ?a ?b] [:call <= ?b ?c] [:lit false]]]
    [lt3           [:call < ?a ?b ?c]                   [:if [:call < ?a ?b] [:call < ?b ?c] [:lit false]]]
    [ge3           [:call >= ?a ?b ?c]                  [:if [:call >= ?a ?b] [:call >= ?b ?c] [:lit false]]]
    [gt3           [:call > ?a ?b ?c]                   [:if [:call > ?a ?b] [:call > ?b ?c] [:lit false]]]
    [eq3           [:call = ?a ?b ?c]                   [:if [:call = ?a ?b] [:call = ?b ?c] [:lit false]]]
    ;; every? and some walk the list
    [every-nil     [:call every? ?f [:nil]]             [:lit true]]
    [every-empty   [:call every? ?f [:sq [:enil]]]      [:lit true]]
    [every-cons    [:call every? ?f [:sq [:econs ?h ?E]]]
                   [:if [:ap ?f ?h] [:call every? ?f [:sq ?E]] [:lit false]]]
    [every-elems   [:call every? ?f [:sq [:elems ?v]]]  [:call every? ?f ?v]]
    [every-app     [:call every? ?f [:sq [:eapp ?A ?B]]]
                   [:if [:call every? ?f [:sq ?A]] [:call every? ?f [:sq ?B]] [:lit false]]]
    [some-nil      [:call some ?f [:nil]]               [:nil]]
    [some-empty    [:call some ?f [:sq [:enil]]]        [:nil]]
    [some-cons     [:call some ?f [:sq [:econs ?h ?E]]]
                   [:if [:ap ?f ?h] [:ap ?f ?h] [:call some ?f [:sq ?E]]]]
    [some-elems    [:call some ?f [:sq [:elems ?v]]]    [:call some ?f ?v]]
    ;; apply + sums; of nothing it is 0
    [apply-sum-nil     [:call apply [:cfn +] [:nil]]                [:lit 0]]
    [apply-sum-empty   [:call apply [:cfn +] [:sq [:enil]]]         [:lit 0]]
    [apply-sum-cons    [:call apply [:cfn +] [:sq [:econs ?a ?E]]]  [:call + ?a [:call apply [:cfn +] [:sq ?E]]]]
    [apply-sum-elems   [:call apply [:cfn +] [:sq [:elems ?v]]]     [:call apply [:cfn +] ?v]]])

(defn- pvar? [x] (and (symbol? x) (str/starts-with? (name x) "?")))

(defn- pvars [pat] (distinct (filter pvar? (tree-seq vector? seq pat))))

(defn- ->logic [pat m]
  (cond (pvar? pat) (get m pat)
        (vector? pat) (mapv #(->logic % m) pat)
        :else pat))

(defn- rule-key [t]
  (when (vector? t)
    (if (= :call (head t)) [:call (second t)] [(head t)])))

(def ^:private indexed
  (delay (group-by (comp rule-key second) pattern-rules)))

(defn- skeleton
  "t cut down to what `pat` inspects: each subterm under a pattern variable
  becomes a placeholder, recorded in `holes`.  core.logic's unification is
  exponential in term size on jolt, so it only ever sees the skeleton."
  [pat x holes]
  (cond
    (pvar? pat) (if (vector? x)
                  (let [h (symbol (str "\u00a7" (count @holes)))]
                    (swap! holes assoc h x)
                    h)
                  x)
    (and (vector? pat) (vector? x) (= (count pat) (count x)))
    (mapv #(skeleton %1 %2 holes) pat x)
    :else x))

(defn- fill-holes [x holes]
  (cond (and (symbol? x) (contains? holes x)) (get holes x)
        (vector? x) (mapv #(fill-holes % holes) x)
        :else x))

(defn match-rule
  "Rewrite t by one pattern rule, or nil: core.logic unifies the rule's
  left side with t's skeleton and reifies its right side."
  [[_ lhs rhs] t]
  (let [holes (atom {})
        sk (skeleton lhs t holes)
        m (zipmap (pvars lhs) (repeatedly l/lvar))
        r (l/run 1 [q] (l/== (->logic lhs m) sk) (l/== q (->logic rhs m)))]
    (when (seq r) (fill-holes (first r) @holes))))

(defn- apply-patterns [rules t]
  (some #(match-rule % t) rules))

;; --- integers ------------------------------------------------------------------

(def ^:private int-types '#{Nat Int})

(declare proved-integer?)

(def ^:private int-list-types '#{(List Nat) (List Int) (Vec Nat) (Vec Int)})

(defn- int-elems?
  "Is every element of this collection an integer, by the types?"
  [ctx c]
  (letfn [(elems-ok? [e]
            (cond
              (symbol? e) (contains? #{{:elems 'Nat} {:elems 'Int}} (get-in ctx [:types e]))
              :else (case (head e)
                      :enil true
                      :econs (and (or (t/int-lit? (nth e 1))
                                      (and (symbol? (nth e 1))
                                           (contains? int-types (get-in ctx [:types (nth e 1)]))))
                                  (elems-ok? (nth e 2)))
                      :eapp (and (elems-ok? (nth e 1)) (elems-ok? (nth e 2)))
                      :elems (int-elems? ctx (second e))
                      false)))]
    (cond
      (symbol? c) (contains? int-list-types (get-in ctx [:types c]))
      (= :nil (head c)) true
      (= :sq (head c)) (elems-ok? (second c))
      :else false)))

(declare int-term?)

(defn- division?
  "quot, mod or rem of an integer by a nonzero integer literal: an integer."
  [ctx t]
  (and (= :call (head t)) (contains? '#{quot mod rem} (second t)) (= 4 (count t))
       (t/int-lit? (nth t 3)) (not (zero? (second (nth t 3))))
       (int-term? ctx (nth t 2))))

(defn int-term?
  "Is t known to be an integer?  Literals, linear forms, counts, variables
  typed Nat or Int, and a term a fact, hypothesis or proved lemma says is
  an integer?.  Nothing else is trusted: not even a fn's signature."
  [ctx t]
  (or (t/int-lit? t)
      (contains? #{:lin} (head t))
      (and (symbol? t) (contains? int-types (get-in ctx [:types t])))
      (and (= :call (head t)) (= 'count (second t)))
      (and (= :call (head t)) (= 'apply (second t)) (= [:cfn '+] (nth t 2 nil))
           (int-elems? ctx (nth t 3 nil)))
      (division? ctx t)
      (and (contains? #{:app :call} (head t)) (proved-integer? ctx t))))

(defn- nat-atom? [ctx a]
  (or (and (symbol? a) (= 'Nat (get-in ctx [:types a])))
      (and (= :call (head a)) (= 'count (second a)))))

(defn- lin-of
  "{:c const :m {atom coef}} for an integer term, else nil."
  [ctx x]
  (cond
    (t/int-lit? x) {:c (second x) :m {}}
    (= :lin (head x)) {:c (second x) :m (into {} (nth x 2))}
    (int-term? ctx x) {:c 0 :m {x 1}}
    :else nil))

(defn- lin+ [a b] {:c (+ (:c a) (:c b)) :m (merge-with + (:m a) (:m b))})
(defn- lin* [k a] {:c (* k (:c a)) :m (into {} (map (fn [[x v]] [x (* k v)])) (:m a))})

(defn lin->term [{:keys [c m]}]
  (let [pairs (vec (sort-by (comp pr-str first) (remove (comp zero? second) m)))]
    (cond (empty? pairs) [:lit c]
          (and (zero? c) (= 1 (count pairs)) (= 1 (second (first pairs)))) (ffirst pairs)
          :else [:lin c pairs])))

(defn- lin-neg-canon
  "A difference d, for d = 0, written so its first coefficient is positive:
  d = 0 and -d = 0 are one fact."
  [lf]
  (let [x (lin->term lf)]
    (if (and (= :lin (head x)) (neg? (second (first (nth x 2)))))
      (lin->term (lin* -1 lf))
      x)))

(defn- all-int? [ctx xs] (every? #(int-term? ctx %) xs))
(defn- all-num-lits? [xs] (every? #(and (t/lit? %) (number? (second %))) xs))

;; --- deciding conditions ---------------------------------------------------------

(defn- gcd [a b] (if (zero? b) (abs a) (recur b (mod a b))))

(defn- tighten
  "c + sum k*x >= 0 over integers, divided through by the gcd of the ks
  with the constant rounded down: 2x - 1 >= 0 is x - 1 >= 0."
  [{:keys [c m]}]
  (let [m (into {} (remove (comp zero? val)) m)
        g (reduce gcd 0 (vals m))]
    (if (> g 1)
      {:c (quot (- c (mod c g)) g) :m (into {} (map (fn [[x k]] [x (quot k g)])) m)}
      {:c c :m m})))

(defn- infeasible?
  "Do these integer constraints, each c + sum k*x >= 0, have no solution?
  Fourier-Motzkin elimination, tightened at each step for integers: a
  true answer is a proof, a false one only means no proof was found."
  [cs]
  (loop [cs (map tighten cs), budget 400]
    (let [cs (distinct cs)]
      (cond
        (some #(and (empty? (:m %)) (neg? (:c %))) cs) true
        (> (count cs) budget) false
        :else
        (if-let [x (first (mapcat (comp keys :m) cs))]
          (let [{pos true neg false} (group-by #(pos? (get-in % [:m x])) (filter #(get-in % [:m x]) cs))
                rest (remove #(get-in % [:m x]) cs)
                combined (for [p pos, q neg
                               :let [a (get-in p [:m x]) b (- (get-in q [:m x]))]]
                           (tighten (lin+ (lin* b p) (lin* a q))))]
            (recur (concat rest combined) budget))
          false)))))

(defn- division-bounds
  "What is known of a division atom, as constraints c + sum k*x >= 0.
  With |k| - 1 = j: (mod n k) is 0..j for k > 0 and -j..0 for k < 0;
  (rem n k) is -j..j; and n - k*(quot n k), the remainder, is -j..j."
  [ctx a]
  (when (division? ctx a)
    (let [[_ f n [_ k]] a
          j (dec (abs k))
          between (fn [lf lo hi] [(lin+ lf {:c (- lo) :m {}}) (lin+ (lin* -1 lf) {:c hi :m {}})])
          self {:c 0 :m {a 1}}]
      (case f
        mod (if (pos? k) (between self 0 j) (between self (- j) 0))
        rem (between self (- j) j)
        quot (when-let [ln (lin-of ctx n)]
               (between (lin+ ln (lin* (- k) self)) (- j) j))))))

(defn- known-constraints
  "The integer facts in ctx, as constraints c + sum k*x >= 0, with each
  Nat atom they or `extra` mention known to be at least 0."
  [ctx extra]
  (let [facts (for [[f v] (:facts ctx)
                    :when (true? v)
                    lf (case (head f)
                         :le (when-let [e (lin-of ctx (second f))] [e])
                         :ieq (when-let [e (lin-of ctx (second f))] [e (lin* -1 e)])
                         nil)]
                lf)
        atoms (distinct (mapcat (comp keys :m) (concat facts extra)))]
    (concat facts
            (for [a atoms :when (nat-atom? ctx a)] {:c 0 :m {a 1}})
            (mapcat #(division-bounds ctx %) atoms))))

(defn decide-le
  "true / false / nil for 0 <= d, from its form, Nat atoms and the facts."
  [ctx d]
  (let [lf (lin-of ctx d)]
    (when lf
      (let [{:keys [c m]} lf
            ks (vals m)
            m* (into {} (remove (comp zero? val)) m)]
        (cond
          (empty? m*) (<= 0 c)
          (and (every? #(nat-atom? ctx %) (keys m*)) (every? pos? (vals m*)) (>= c 0)) true
          (and (every? #(nat-atom? ctx %) (keys m*)) (every? neg? (vals m*)) (< c 0)) false
          :else
          (let [known (known-constraints ctx [lf])]
            (cond
              ;; d <= -1 contradicts what is known: 0 <= d
              (infeasible? (cons (lin+ (lin* -1 lf) {:c -1 :m {}}) known)) true
              ;; 0 <= d contradicts it: d < 0
              (infeasible? (cons lf known)) false
              :else nil)))))))

(defn decide-ieq [ctx d]
  (let [lf (lin-of ctx d)]
    (when lf
      (cond
        (empty? (remove (comp zero? val) (:m lf))) (zero? (:c lf))
        (contains? (:facts ctx) [:ieq d]) (get (:facts ctx) [:ieq d])
        (or (true? (decide-le ctx (lin->term (lin+ lf {:c -1 :m {}}))))
            (true? (decide-le ctx (lin->term (lin+ (lin* -1 lf) {:c -1 :m {}}))))) false
        :else nil))))

(defn decide
  "The truth of condition c under ctx, or nil when it is open."
  [ctx c]
  (cond
    (= :le (head c)) (let [f (get (:facts ctx) c)] (if (some? f) f (decide-le ctx (second c))))
    (= :ieq (head c)) (decide-ieq ctx (second c))
    (contains? (:facts ctx) c) (get (:facts ctx) c)
    :else nil))

(def ^:private seq-makers
  "clojure.core fns that always return a seq or vector object, which is
  truthy whatever it holds.  A lazy one is truthy before it is realised,
  so its elements must not be computed to decide it."
  '#{filter map concat rest cons list vector vec})

(defn truthiness
  "true / false for a term whose truthiness is settled, else nil.  An if
  whose branches agree has their truthiness without its test being run:
  a lazy seq's elements can hide behind such an if, and computing them
  could throw where the seq, unrealised, would not."
  [ctx c]
  (case (head c)
    :nil false
    :lit (not (false? (second c)))
    (:sq :fn :cfn :dfn) true
    :if (let [a (truthiness ctx (nth c 2)) b (truthiness ctx (nth c 3))]
          (when (and (some? a) (= a b)) a))
    :call (if (contains? seq-makers (second c))
            true
            (let [d (decide ctx c)] (when (some? d) d)))
    (let [d (decide ctx c)] (when (some? d) d))))

;; --- equality ------------------------------------------------------------------

(def ^:private float-free-types
  '#{Nat Int Bool String Keyword Symbol Char Unit})

(defn- float-free-type?
  "seen: the data types already being checked; a field of one of them is
  float-free if the rest of the type is."
  ([ctx ty] (float-free-type? ctx ty #{}))
  ([ctx ty seen]
   (cond
     (contains? float-free-types ty) true
     (contains? seen ty) true
     (and (seq? ty) (contains? '#{List Vec} (first ty))) (float-free-type? ctx (second ty) seen)
     (and (map? ty) (:elems ty)) (float-free-type? ctx (:elems ty) seen)
     (and (symbol? ty) (get-in ctx [:tenv ty]))
     (every? (fn [[_ c]] (every? #(float-free-type? ctx % (conj seen ty)) (:fields c)))
             (:ctors (get-in ctx [:tenv ty])))
     :else false)))

(declare boolean-term?)

(def ^:private selecting-fns
  "clojure.core fns whose value is made of parts of their data arguments
  and nothing else: no float in, no float out.  A fn argument only picks
  which parts."
  '#{filter remove concat list vector vec cons rest next seq take drop reverse
     sort distinct butlast first second last nth})

(defn float-free?
  "Can this term's value hold no float?  Then two syntactically equal
  terms are =; with a NaN inside, Clojure's = says they are not.  A value
  built only by picking and arranging parts of float-free values -- a
  filter, a concat, a fold that does no more, a definition that does no
  more -- has none either."
  ([ctx x] (float-free? ctx x #{} #{}))
  ([ctx x env seen]
   (let [ff? #(float-free? ctx % env seen)]
     (cond
       (int-term? ctx x) true
       (boolean-term? x) true
       (symbol? x) (or (contains? env x) (float-free-type? ctx (get-in ctx [:types x])))
       :else
       (case (head x)
         :nil true
         :bottom true
         :lit (not (float? (second x)))
         :sq (ff? (second x))
         :enil true
         :econs (and (ff? (nth x 1)) (ff? (nth x 2)))
         :eapp (and (ff? (nth x 1)) (ff? (nth x 2)))
         :elems (ff? (second x))
         :if (and (ff? (nth x 2)) (ff? (nth x 3)))
         :call (let [[_ f & args] x]
                 (cond
                   (contains? selecting-fns f)
                   (every? ff? (remove #(contains? #{:fn :cfn :dfn} (head %)) args))
                   ;; a fold whose step makes its value of the accumulator's
                   ;; and the element's parts
                   (and (= 'reduce f) (= 3 (count args)) (= :fn (head (first args)))
                        (= 2 (count (second (first args)))))
                   (let [[[_ ps body] init coll] args]
                     (and (ff? init) (ff? coll)
                          (float-free? ctx body (into env ps) seen)))
                   :else false))
         ;; a definition's value, on float-free arguments, when its body
         ;; makes it of their parts; a recursive call is taken to, which
         ;; holds of every value the definition returns
         :app (let [[_ f & args] x
                    d (get-in ctx [:defs f])]
                (and (:params d) (= (count args) (count (:params d)))
                     (every? ff? args)
                     (or (contains? seen f)
                         (float-free? ctx (:body d) (set (:params d)) (conj seen f)))))
         false)))))

(defn- exact-scalar?
  "A value = compares by identity of value: two of them are = exactly when
  they are the same, and = to a third agrees with either."
  [v]
  (or (keyword? v) (string? v) (boolean? v) (char? v) (symbol? v) (integer? v)))

(defn- known-literal
  "The exact literal term t is known to equal, from the facts."
  [ctx t]
  (first (for [[c v] (:facts ctx)
               :when (and (true? v) (= :call (head c)) (= '= (second c)) (= 3 (count (rest c)))
                          (= t (nth c 2)) (= :lit (head (nth c 3))) (exact-scalar? (second (nth c 3))))]
           (second (nth c 3)))))

(defn- equality [ctx a b]
  (let [ha (head a) hb (head b)]
    (cond
      (and (= :lit ha) (= :lit hb)) [:lit (= (second a) (second b))]
      (and (= :nil ha) (= :nil hb)) [:lit true]
      (and (= :nil ha) (contains? #{:lit :sq} hb)) [:lit false]
      (and (= :nil hb) (contains? #{:lit :sq} ha)) [:lit false]
      (or (and (= :lit ha) (= :sq hb)) (and (= :sq ha) (= :lit hb))) [:lit false]
      (and (= :sq ha) (= :sq hb))
      (let [ea (second a) eb (second b)]
        (cond
          (and (= :enil (head ea)) (= :enil (head eb))) [:lit true]
          (and (= :enil (head ea)) (= :econs (head eb))) [:lit false]
          (and (= :econs (head ea)) (= :enil (head eb))) [:lit false]
          (and (= :econs (head ea)) (= :econs (head eb)))
          [:if [:call '= (nth ea 1) (nth eb 1)]
               [:call '= [:sq (nth ea 2)] [:sq (nth eb 2)]]
               [:lit false]]
          ;; the same float-free elements first: the rest decides
          (and (= :eapp (head ea)) (= :eapp (head eb)) (= (nth ea 1) (nth eb 1))
               (float-free? ctx (nth ea 1)))
          [:call '= [:sq (nth ea 2)] [:sq (nth eb 2)]]
          (and (= a b) (float-free? ctx a)) [:lit true]
          :else nil))
      (and (int-term? ctx a) (int-term? ctx b))
      [:ieq (lin-neg-canon (lin+ (lin-of ctx a) (lin* -1 (lin-of ctx b))))]
      (and (= a b) (float-free? ctx a)) [:lit true]
      ;; a literal goes second, so a fact and a test of it are one term
      (and (= :lit ha) (not= :lit hb)) [:call '= b a]
      ;; a term known to equal one exact literal is not another
      (and (= :lit hb) (exact-scalar? (second b)))
      (when-let [v (known-literal ctx a)]
        [:lit (= v (second b))])
      :else nil)))

;; --- computed rules --------------------------------------------------------------

(defn- insert-sorted
  "A fn value inserting x into a sorted list s of integers: the elements
  below x, then x, then the elements above it -- or at and above it, when
  duplicates are kept."
  [above]
  [:fn '[s x] [:call 'concat
               [:call 'filter [:fn '[y] [:call '< 'y 'x]] 's]
               [:call 'list 'x]
               [:call 'filter [:fn '[y] [:call above 'y 'x]] 's]]])

(defn sort-model
  "(sort xs) and (sort (distinct xs)) on a list of integers, as a fold
  inserting each element into the sorted list so far.  Only on integers:
  two equal integers are the same value, so where an equal element goes
  does not matter, and < orders them totally.  nil when xs is not known
  to hold integers."
  [ctx a]
  (let [dedup? (and (= :call (head a)) (= 'distinct (second a)) (= 3 (count a)))
        xs (if dedup? (nth a 2) a)]
    (when (int-elems? ctx xs)
      [:call 'reduce (insert-sorted (if dedup? '> '>=)) [:sq t/enil] xs])))

(defn- le [ctx a b]
  [:le (lin->term (lin+ (lin-of ctx b) (lin* -1 (lin-of ctx a))))])

(defn- lt [ctx a b]
  [:le (lin->term (lin+ (lin+ (lin-of ctx b) (lin* -1 (lin-of ctx a))) {:c -1 :m {}}))])

(defn- nth-rule [v i d]
  (let [miss (if (= ::none d) [:bottom] d)]
    (cond
      (= :nil (head v)) (if (= ::none d) [:nil] d)
      (neg? i) miss
      (= :sq (head v))
      (let [e (second v)]
        (case (head e)
          :enil miss
          :econs (if (zero? i) (nth e 1)
                     (if (= ::none d)
                       [:call 'nth [:sq (nth e 2)] [:lit (dec i)]]
                       [:call 'nth [:sq (nth e 2)] [:lit (dec i)] d]))
          :elems (if (= ::none d)
                   [:call 'nth (second e) [:lit i]]
                   [:call 'nth (second e) [:lit i] d])
          nil))
      :else nil)))

(defn- reduced-free?
  "Can fn value f never return a `reduced`?  Then reduce runs it over the
  whole collection.  A core fn value can't (reduced itself is outside the
  model), nor can a fn literal whose calls reach only definitions the
  prover read, since none of those can call reduced either.  A call of an
  unknown fn value could."
  ([ctx f] (reduced-free? ctx f #{}))
  ([ctx f seen]
   (case (head f)
     :cfn (not (contains? '#{reduced ensure-reduced} (second f)))
     :fn (every? (fn [x]
                   (case (head x)
                     :ap (reduced-free? ctx (second x) seen)
                     :app (let [q (second x) d (get-in ctx [:defs q])]
                            (or (contains? seen q)
                                (and (:params d) (reduced-free? ctx [:fn (:params d) (:body d)]
                                                                (conj seen q)))))
                     true))
                 (t/subterms (nth f 2)))
     false)))

(defn- reduce-rule
  "(reduce f init coll), one step: an empty coll gives init, a head
  goes into the accumulator, and concatenated colls fold one after the
  other."
  [ctx f init coll]
  (let [e (when (= :sq (head coll)) (second coll))]
    (cond
      (= :nil (head coll)) init
      (= :enil (head e)) init
      (not (reduced-free? ctx f)) nil
      (= :econs (head e)) [:call 'reduce f [:ap f init (nth e 1)] [:sq (nth e 2)]]
      (= :eapp (head e)) [:call 'reduce f [:call 'reduce f init [:sq (nth e 1)]] [:sq (nth e 2)]]
      (= :elems (head e)) [:call 'reduce f init (second e)]
      :else nil)))

(def ^:private pure-fns
  "clojure.core fns that compute a value from plain data and nothing else,
  so a call of one on closed values is its value."
  '#{sort distinct reverse hash-set set sort-by count vec str name keyword
     subs frequencies max min abs quot mod rem inc dec + - * nth first second
     last rest butlast take drop concat interpose})

(defn- closed-value
  "The Clojure value of a closed term built from literals, or ::none."
  [x]
  (case (head x)
    :lit (second x)
    :nil nil
    :sq (let [vs (loop [e (second x), out []]
                   (case (head e)
                     :enil out
                     :econs (let [v (closed-value (nth e 1))] (if (= ::none v) nil (recur (nth e 2) (conj out v))))
                     nil))]
          (if (nil? vs) ::none (apply list vs)))
    :call (if (= 'hash-set (second x))
            (let [vs (map closed-value (drop 2 x))] (if (some #{::none} vs) ::none (set vs)))
            ::none)
    ::none))

(defn- value-term
  "The term for a plain value: a literal, a sequential or a set of them."
  [v]
  (cond (sequential? v) (let [ts (map value-term v)] (when (every? some? ts) (t/seq-term ts)))
        (set? v) (let [ts (map value-term (sort-by pr-str v))] (when (every? some? ts) (into [:call 'hash-set] ts)))
        (or (map? v) (fn? v)) nil
        :else (t/lit v)))

(defn- ground-call
  "A pure core fn applied to closed values, computed: the code is pure,
  so running it is its meaning.  nil when it is not closed or throws."
  [x]
  (when (and (= :call (head x)) (contains? pure-fns (second x)))
    (let [vs (map closed-value (drop 2 x))]
      (when (not-any? #{::none} vs)
        (try (value-term (let [r (apply @(resolve (symbol "clojure.core" (name (second x)))) vs)]
                           (if (seq? r) (doall r) r)))
             (catch Throwable _ nil))))))

(defn- computed
  "The computed rules: a rewrite of t, or nil."
  [ctx x]
  (case (head x)
    :call
    (or
     (when-not (= 'hash-set (second x)) (ground-call x))
     (let [[_ f & args] x
          n (count args)
          [a b] args]
      (case f
        + (cond (all-num-lits? args) [:lit (apply + (map second args))]
                (all-int? ctx args) (lin->term (reduce lin+ {:c 0 :m {}} (map #(lin-of ctx %) args)))
                :else nil)
        - (cond (all-num-lits? args) [:lit (apply - (map second args))]
                (and (pos? n) (all-int? ctx args))
                (lin->term (if (= 1 n)
                             (lin* -1 (lin-of ctx a))
                             (reduce lin+ (lin-of ctx a) (map #(lin* -1 (lin-of ctx %)) (rest args)))))
                :else nil)
        inc (cond (all-num-lits? args) [:lit (inc (second a))]
                  (int-term? ctx a) (lin->term (lin+ (lin-of ctx a) {:c 1 :m {}}))
                  :else nil)
        dec (cond (all-num-lits? args) [:lit (dec (second a))]
                  (int-term? ctx a) (lin->term (lin+ (lin-of ctx a) {:c -1 :m {}}))
                  :else nil)
        * (cond (all-num-lits? args) [:lit (apply * (map second args))]
                (and (all-int? ctx args) (<= (count (remove t/int-lit? args)) 1))
                (let [k (apply * (map second (filter t/int-lit? args)))
                      v (first (remove t/int-lit? args))]
                  (lin->term (if v (lin* k (lin-of ctx v)) {:c k :m {}})))
                :else nil)
        (< <= > >=)
        (when (= 2 n)
          (cond (all-num-lits? args) [:lit ((resolve f) (second a) (second b))]
                (all-int? ctx args) (case f
                                      <= (le ctx a b)
                                      < (lt ctx a b)
                                      >= (le ctx b a)
                                      > (lt ctx b a))
                :else nil))
        zero? (when (int-term? ctx a) [:ieq (lin-neg-canon (lin-of ctx a))])
        pos? (when (int-term? ctx a) (lt ctx [:lit 0] a))
        neg? (when (int-term? ctx a) (lt ctx a [:lit 0]))
        = (when (= 2 n) (equality ctx a b))
        not (cond
              (= :le (head a)) [:le (lin->term (lin+ (lin* -1 (lin-of ctx (second a))) {:c -1 :m {}}))]
              :else (let [tr (truthiness ctx a)] (when (some? tr) [:lit (not tr)])))
        list (t/seq-term args)
        vector (t/seq-term args)
        vec (when (= 1 n) [:sq [:elems a]])
        concat (if (empty? args)
                 [:sq t/enil]
                 [:sq (reduce (fn [e v] [:eapp [:elems v] e])
                              [:elems (last args)] (reverse (butlast args)))])
        identity (when (= 1 n) a)
        (bit-shift-left bit-shift-right)
        (when (and (= 2 n) (t/int-lit? a) (t/int-lit? b) (<= 0 (second b) 62))
          [:lit ((case f bit-shift-left bit-shift-left bit-shift-right bit-shift-right)
                 (second a) (second b))])
        (quot mod rem) (when (and (= 2 n) (all-num-lits? args) (integer? (second a))
                                  (integer? (second b)) (not (zero? (second b))))
                         [:lit ((case f quot quot mod mod rem rem) (second a) (second b))])
        integer? (when (= 1 n)
                   (cond (int-term? ctx a) [:lit true]
                         (or (= :nil (head a)) (= :sq (head a))
                             (and (t/lit? a) (not (integer? (second a))))) [:lit false]
                         :else nil))
        reduce (when (= 3 n) (reduce-rule ctx a b (nth args 2)))
        sort (when (= 1 n) (sort-model ctx a))
        nth (when (and (<= 2 n 3) (t/int-lit? b))
              (nth-rule a (second b) (if (= 3 n) (nth args 2) ::none)))
        nil)))

    :ap (let [[_ f & args] x]
          (cond
            (and (= :fn (head f)) (= (count (second f)) (count args)))
            (t/subst (nth f 2) (zipmap (second f) args))
            ;; a core fn value applied is a call of it, and a defn's an app
            (= :cfn (head f)) (into [:call (second f)] args)
            (= :dfn (head f)) (into [:app (second f)] args)
            :else nil))

    :le (let [d (decide ctx x)] (when (some? d) [:lit d]))
    :ieq (let [d (decide ctx x)] (when (some? d) [:lit d]))
    nil))

;; --- normalising ------------------------------------------------------------------

(defn- out-of-fuel! []
  (throw (ex-info "out of fuel" {::fuel true})))

(def ^:dynamic *last-terms*
  "When bound to an atom, keeps the terms rewritten as fuel runs low, for
  debugging a rewrite that does not terminate."
  nil)

(defn- burn!
  ([ctx] (burn! ctx nil))
  ([ctx x]
   (let [left (swap! (:fuel ctx) dec)]
     (when (and *last-terms* x (< left 60)) (swap! *last-terms* conj x))
     (when (neg? left) (out-of-fuel!)))))

(declare normalize)

(defn- splittable? [c]
  (or (contains? #{:le :ieq} (head c))
      (and (= :call (head c)) (= 'not (second c)) (= :ieq (head (nth c 2))))))

(defn open-conditions
  "The conditions of the undecided ifs in t."
  [t]
  (keep (fn [x] (when (= :if (head x)) (nth x 1))) (t/subterms t)))

(declare assume truthiness)

(defn- settled?
  "Should a recursive definition, its arguments substituted in, be
  unfolded?  Its guards -- the tests of its if-tree, from the top -- are
  decided one by one, following the branch each takes.  It is unfolded
  when every guard left open is an integer comparison the prover can
  split on.  An open test on the shape of an unknown value (seq xs,
  first t) means it is too early: the call stays folded until induction
  or a split reveals that shape.  Once a guard has been decided, an open
  test of what a definition's call returns -- (and (bst? l) ...) after
  the tag is known -- is not a shape: the call stays folded until its
  own guards settle.  Only the guards are normalised, never the
  branches, so a recursive call inside a branch is not unfolded here."
  ([ctx body] (settled? ctx body false))
  ([ctx body decided?]
   (if (= :if (head body))
     (let [c (normalize ctx (nth body 1))
           tr (truthiness ctx c)]
       (cond
         (true? tr) (settled? ctx (nth body 2) true)
         (false? tr) (settled? ctx (nth body 3) true)
         (and (= :call (head c)) (= 'not (second c)))
         (settled? ctx [:if (nth c 2) (nth body 3) (nth body 2)] decided?)
         (splittable? c) (and (settled? (assume ctx c true) (nth body 2) decided?)
                              (settled? (assume ctx c false) (nth body 3) decided?))
         (and decided? (some #(= :app (head %)) (t/subterms c)))
         (and (settled? ctx (nth body 2) true) (settled? ctx (nth body 3) true))
         :else false))
     true)))

(defn- unfold [ctx x]
  (let [[_ f & args] x
        d (get-in ctx [:defs f])]
    (when (and d (= (count (:params d)) (count args))
               (not (contains? @(:stuck ctx) x)))
      (burn! ctx)
      (let [body (t/subst (:body d) (zipmap (:params d) args))]
        (if-not (:recursive? d)
          (do (swap! (:unfolded ctx) conj f) body)
          (if (settled? ctx body)
            (do (swap! (:unfolded ctx) conj f) body)
            (do (swap! (:stuck ctx) conj x) nil)))))))

(declare match-term)

(defn- loops?
  "Would rewriting x to y only put x back inside a bigger term?"
  [x y]
  (and (not= x y) (some #(= x %) (t/subterms y))))

(defn- ih-rewrite
  "Rewrite x by an induction hypothesis.  One with free variables (its
  law quantified over them as well) matches x as a pattern, and holds
  only for their declared types, which its hypothesis states."
  [ctx x]
  (some (fn [{:keys [hyp lhs rhs vars]}]
          ;; a hypothesis whose left side is a bare variable would match
          ;; every term; it has nothing to rewrite
          (when-let [m (when-not (symbol? lhs)
                         (if (seq vars) (match-term lhs x vars) (when (= x lhs) {})))]
            (let [hyp (some-> hyp (t/subst m))
                  y (t/subst rhs m)]
              ;; a rewrite to x itself changes nothing, and its hypothesis
              ;; may hold x: reading it would rewrite x again
              (when (and (not= x y)
                         (not (loops? x y))
                         (or (nil? hyp) (true? (truthiness ctx (normalize ctx hyp)))))
                (swap! (:used-ih ctx) inc)
                y))))
        (:ih ctx)))

(defn match-term
  "Bindings of pattern variables `vs` that make `pat` equal to x, or nil."
  ([pat x vs] (match-term pat x vs {}))
  ([pat x vs m]
   (cond
     (nil? m) nil
     (and (symbol? pat) (contains? vs pat))
     (if (contains? m pat) (when (= (get m pat) x) m) (assoc m pat x))
     ;; fn literals match up to the names of their parameters
     (and (= :fn (head pat)) (= :fn (head x)) (= (count (second pat)) (count (second x))))
     (match-term (t/subst (nth pat 2) (zipmap (second pat) (second x))) (nth x 2) vs m)
     (and (vector? pat) (vector? x) (= (count pat) (count x)))
     (reduce (fn [m [p y]] (or (match-term p y vs m) (reduced nil))) m (map vector pat x))
     (= pat x) m
     :else nil)))

(declare normalize truthiness ih-rewrite lemma-rewrite)

(defn- proved-integer?
  "Does a fact, an induction hypothesis or a proved lemma say (integer? t)?"
  [ctx t]
  (let [memo (:int-memo ctx)
        hit (some-> memo deref (get t))]
    (if (some? hit)
      hit
      (let [q [:call 'integer? t]
            _ (some-> memo (swap! assoc t false))  ; no circular answer while working it out
            r (boolean (or (true? (get (:facts ctx) q))
                           (= [:lit true] (ih-rewrite ctx q))
                           (= [:lit true] (lemma-rewrite ctx q))))]
        (some-> memo (swap! assoc t r))
        r))))

(defn- conjuncts
  "The parts of a normalised conjunction: (if a b false) and (if a b a),
  the shapes `and` lowers to."
  [h]
  (if (and (= :if (head h)) (or (= [:lit false] (nth h 3)) (= (nth h 1) (nth h 3))))
    (concat (conjuncts (nth h 1)) (conjuncts (nth h 2)))
    [h]))

(defn- bind-free
  "Every extension of bindings m that gives the variables of hyp that the
  left side left unbound a value from the facts: a part of hyp that
  mentions one is matched against a fact known to be true, the way ACL2
  binds a hypothesis's free variables.  Parts that are integer
  comparisons go last: their linear form orders terms by name, so they
  are checked once bound, not matched."
  [ctx hyp vars m]
  (let [unbound? (fn [m c] (some #(and (contains? vars %) (not (contains? m %))) (t/vars c)))
        [plain arith] ((juxt remove filter) #(contains? #{:le :ieq} (head %)) (conjuncts hyp))
        facts (sort-by pr-str (for [[f v] (:facts ctx) :when (true? v)] f))]
    (letfn [(go [m cs]
              (if-let [c (first cs)]
                (if (unbound? m c)
                  (mapcat #(some-> (match-term c % vars m) (go (rest cs))) facts)
                  (go m (rest cs)))
                [m]))]
      (go m (concat plain arith)))))

(defn- lemma-rewrite
  "Rewrite x by an earlier proved law: its left side matched against x,
  its hypothesis, instantiated, normalised to true here.  A variable of
  the hypothesis the left side does not bind is bound from the facts."
  [ctx x]
  (some (fn [{:keys [vars hyp lhs rhs name]}]
          (when-let [m0 (match-term lhs x vars)]
            (some (fn [m]
                    (when (every? #(contains? m %) (t/vars rhs))
                      (let [y (t/subst rhs m)]
                        (when (and (not= x y)
                                   (not (loops? x y))
                                   (or (nil? hyp)
                                       (let [h (t/subst hyp m)]
                                         (and (every? #(not (contains? vars %)) (t/vars h))
                                              (true? (truthiness ctx (normalize ctx h)))))))
                          (swap! (:lemmas-used ctx) conj name)
                          y))))
                  (if (and hyp (some #(and (contains? vars %) (not (contains? m0 %))) (t/vars hyp)))
                    (bind-free ctx hyp vars m0)
                    [m0]))))
        (:lemmas ctx)))

(def ^:private boolean-fns
  '#{= not= not < <= > >= empty? zero? pos? neg? even? odd? nil? some? true? false? every? boolean})

(defn- boolean-term?
  "Does t return true or false, never another value?  Only then is an
  assumed test the value true or false: (seq xs) assumed true is not true."
  [t]
  (case (head t)
    (:le :ieq) true
    :lit (boolean? (second t))
    :call (or (contains? boolean-fns (second t))
              ;; apply of a comparison
              (and (= 'apply (second t)) (= :cfn (head (nth t 2 nil)))
                   (contains? '#{< <= > >= =} (second (nth t 2)))))
    false))

(defn- lift-if
  "A core fn call with an if among its arguments, as an if of two calls:
  a call runs its arguments first, so the test runs either way.  Only the
  first such argument is lifted; normalising the branches lifts the rest."
  [x]
  (when (= :call (head x))
    (let [args (vec (drop 2 x))
          i (first (keep-indexed (fn [i a] (when (= :if (head a)) i)) args))]
      (when i
        (let [[_ c a b] (nth args i)
              with (fn [v] (into [:call (second x)] (assoc args i v)))]
          [:if c (with a) (with b)])))))

(defn- step [ctx x]
  (or (ih-rewrite ctx x)
      (lemma-rewrite ctx x)
      (lift-if x)
      (when (and (contains? (:facts ctx) x) (not (contains? #{:le :ieq} (head x)))
                 (boolean-term? x) (boolean? (get (:facts ctx) x)))
        [:lit (get (:facts ctx) x)])
      (apply-patterns (get @indexed (rule-key x)) x)
      (computed ctx x)
      (when (= :app (head x)) (unfold ctx x))))

(defn assume
  "ctx with condition c taken to be v.  A false 0 <= d is also kept as
  0 <= -d-1, the form the integer reasoning reads."
  [ctx c v]
  (if (and (= :call (head c)) (= 'not (second c)) (boolean? v))
    (assume ctx (nth c 2) (not v))
  (let [facts (assoc (:facts ctx) c v)
        facts (if (and (= :le (head c)) (false? v) (lin-of ctx (second c)))
                (assoc facts [:le (lin->term (lin+ (lin* -1 (lin-of ctx (second c))) {:c -1 :m {}}))] true)
                facts)]
    (assoc ctx :facts facts :memo (atom {}) :stuck (atom #{}) :int-memo (atom {})))))

(defn- fn-height
  "How deep fn literals nest in t: 0 with none."
  [t]
  (if (vector? t)
    (+ (if (= :fn (head t)) 1 0) (reduce max 0 (map fn-height (rest t))))
    0))

(defn- canonical-params
  "A fn literal's parameters, named by their position and by how deep fn
  literals nest in its body, so two fns that differ only in the names of
  their parameters are one term, and a fact about one is a fact about the
  other.  An inner fn's parameters are never named like an outer one's:
  the outer's height is greater."
  [ps body]
  (let [h (inc (fn-height body))]
    (mapv #(symbol (str "%" h "_" %)) (range (count ps)))))

(defn normalize
  "Rewrite t to normal form under ctx.  An if whose test is open gets its
  branches normalised under the test assumed true, and false."
  [ctx x]
  (if-let [hit (get @(:memo ctx) x)]
    hit
    (let [r (cond
              (symbol? x) x
              (not (vector? x)) x
              (contains? #{:lit :nil :enil :bottom :cfn} (head x)) x
              :else
              (let [x* (case (head x)
                         :if (let [c (normalize ctx (nth x 1))
                                   tr (truthiness ctx c)]
                               (cond
                                 (true? tr) (normalize ctx (nth x 2))
                                 (false? tr) (normalize ctx (nth x 3))
                                 (and (= :call (head c)) (= 'not (second c)))
                                 (normalize ctx [:if (nth c 2) (nth x 3) (nth x 2)])
                                 :else
                                 (let [a (normalize (assume ctx c true) (nth x 2))
                                       b (normalize (assume ctx c false) (nth x 3))]
                                   (cond (= a b) a
                                         ;; (if c true false) is c when c is a boolean
                                         (and (= [:lit true] a) (= [:lit false] b) (boolean-term? c)) c
                                         :else [:if c a b]))))
                         :lin (let [[_ c pairs] x
                                    atoms (map (fn [[a k]] [(normalize ctx a) k]) pairs)]
                                (if (every? #(int-term? ctx (first %)) atoms)
                                  (lin->term (reduce lin+ {:c c :m {}}
                                                     (map (fn [[a k]] (lin* k (lin-of ctx a))) atoms)))
                                  [:lin c (vec atoms)]))
                         :fn (let [[_ ps body] x
                                   ps* (canonical-params ps body)]
                               [:fn ps* (normalize ctx (t/subst body (zipmap ps ps*)))])
                         (into [(head x)] (map #(normalize ctx %)) (rest x)))]
                (if (= :if (head x))
                  ;; a boolean law's left side is often an if: an induction
                  ;; hypothesis or a lemma may still rewrite the whole of one
                  (if-let [y (and (= :if (head x*))
                                  (or (ih-rewrite ctx x*) (lemma-rewrite ctx x*)))]
                    (do (burn! ctx) (normalize ctx y))
                    x*)
                  (do (burn! ctx x*)
                      (if-let [y (step ctx x*)]
                        (if (= y x*) x* (normalize ctx y))
                        x*)))))]
      (swap! (:memo ctx) assoc x r)
      r)))

(defn context
  "A fresh normalising context.  defs: name -> {:params :body :recursive?};
  types: variable -> type; tenv: data declarations."
  [{:keys [defs types tenv facts ih fuel lemmas lemmas-used]}]
  {:defs (or defs {}) :types (or types {}) :tenv (or tenv {})
   :facts (or facts {}) :ih (or ih []) :lemmas (or lemmas [])
   :lemmas-used (or lemmas-used (atom #{}))
   :memo (atom {}) :stuck (atom #{}) :unfolded (atom #{}) :used-ih (atom 0) :int-memo (atom {})
   :fuel (atom (or fuel 20000))})

;; --- checking the rules against the runtime ----------------------------------------

(def ^:private sample-fns
  [[:fn '[p] [:call 'inc 'p]]
   [:fn '[p] [:call 'odd? 'p]]
   [:fn '[p] [:call '< 'p [:lit 3]]]
   [:fn '[p] [:call 'list 'p 'p]]])

(def ^:private gen-int (gen/choose -5 5))

(def ^:private gen-value
  (gen/frequency [[1 (gen/return nil)]
                  [3 gen-int]
                  [3 (gen/one-of [(gen/list gen-int) (gen/vector gen-int)])]
                  [1 (gen/list (gen/list gen-int))]]))

(defn- gen-for [v]
  (let [n (name v)]
    (cond
      (contains? #{"?E" "?A" "?B" "?C"} n) (gen/fmap (fn [xs] [:term (t/elems-of (map t/value->term xs))])
                                                     (gen/list gen-int))
      (= "?f" n) (gen/fmap (fn [f] [:term f]) (gen/elements sample-fns))
      (= "?p" n) (gen/return [:term '[p]])
      (= "?b" n) (gen/return [:term [:lit 1]])
      :else (gen/fmap (fn [x] [:term (t/value->term x)]) gen-value))))

(defn- realize
  "Force every lazy seq inside v, so a throw during realisation counts as
  the term not returning -- laws compare realised values."
  [v]
  (cond (seq? v) (doall (map realize v))
        (coll? v) (do (doseq [x v] (realize x)) v)
        :else v))

(defn- returns [f]
  (try [:ok (realize (f))] (catch Throwable _ nil)))

(defn check-rule
  "Check one pattern rule against the runtime: whenever its left side
  returns a value, its right side returns an = value."
  [[nm lhs rhs] trials seed]
  (let [vs (vec (pvars lhs))
        p (prop/for-all* (mapv gen-for vs)
            (fn [& terms]
              (let [m (zipmap vs (map second terms))
                    fill (fn fill [x] (cond (pvar? x) (get m x)
                                            (vector? x) (mapv fill x)
                                            :else x))
                    l (returns #(t/evaluate (fill lhs)))]
                (or (nil? l)
                    (let [r (returns #(t/evaluate (fill rhs)))]
                      (and r (= (second l) (second r))))))))
        res (tc/quick-check trials p :seed seed)]
    (if (:pass? res)
      {:rule nm :ok true}
      {:rule nm :ok false :counterexample (get-in res [:shrunk :smallest])})))

(defn self-test
  "Check every pattern rule (or `rules`) against the runtime."
  ([] (self-test pattern-rules 200 42))
  ([rules trials seed]
   (let [rs (mapv #(check-rule % trials seed) rules)]
     {:ok (every? :ok rs) :failures (vec (remove :ok rs)) :checked (count rs)})))

;; --- ground terms: the normaliser against the runtime ----------------------------

(def ^:private unary '[seq first rest next second empty? count not vec])

(defn- gen-ground [depth]
  (let [leaf (gen/fmap t/value->term gen-value)
        int-leaf (gen/fmap #(vector :lit %) gen-int)]
    (if (zero? depth)
      (gen/one-of [leaf int-leaf])
      (let [sub (gen-ground (dec depth))]
        (gen/one-of
          [leaf
           (gen/fmap (fn [[f x]] [:call f x]) (gen/tuple (gen/elements unary) sub))
           (gen/fmap (fn [[f x y]] [:call f x y])
                     (gen/tuple (gen/elements '[cons concat list =]) sub sub))
           (gen/fmap (fn [[f x y]] [:call f x y])
                     (gen/tuple (gen/elements '[+ - < <= = max]) int-leaf int-leaf))
           (gen/fmap (fn [[x i]] [:call 'nth x [:lit i] [:nil]]) (gen/tuple sub (gen/choose -1 3)))
           ;; nth with no default only on nil and plain lists: on jolt, nth
           ;; past the end of an empty lazy seq is nil while on () it throws,
           ;; and the model has one empty sequential, so it says [:bottom]
           (gen/fmap (fn [[x i]] [:call 'nth x [:lit i]])
                     (gen/tuple (gen/one-of [(gen/return t/tnil) leaf]) (gen/choose -1 3)))
           (gen/fmap (fn [[f g x]] [:call f g x])
                     (gen/tuple (gen/elements '[filter map]) (gen/elements sample-fns) sub))
           (gen/fmap (fn [[c a b]] [:if c a b]) (gen/tuple sub sub sub))
           (gen/fmap (fn [[f x]] [:call 'apply [:cfn f] x])
                     (gen/tuple (gen/elements '[<= < >= > +]) sub))
           (gen/fmap (fn [[f i x]] [:call 'reduce f i x])
                     (gen/tuple (gen/elements [[:cfn '+] [:cfn 'max]
                                               [:fn '[a b] [:call '+ 'a [:lit 1]]]
                                               [:fn '[a b] [:call 'cons 'b 'a]]])
                                int-leaf sub))
           (gen/fmap (fn [x] [:call 'integer? x]) sub)])))))

(defn ground-check
  "Normalise random closed terms and run both: wherever the original
  returns, the normal form returns an = value."
  ([] (ground-check 300 42))
  ([trials seed]
   (let [p (prop/for-all [x (gen-ground 3)]
             (let [o (returns #(t/evaluate x))]
               (or (nil? o)
                   (let [n (returns #(t/evaluate (normalize (context {}) x)))]
                     (and n (= (second o) (second n)))))))
         res (tc/quick-check trials p :seed seed)]
     (if (:pass? res)
       {:ok true}
       {:ok false :counterexample (first (get-in res [:shrunk :smallest]))}))))

;; --- the models of clojure.core fns against the runtime -------------------------

(defn model-check
  "Run the sort model on random lists of integers -- lists, vectors and
  nil, with and without distinct -- against sort itself."
  ([] (model-check 300 42))
  ([trials seed]
   (let [ctx (context {:types '{xs (List Int)}})
         p (prop/for-all [xs (gen/one-of [(gen/return nil) (gen/list gen-int) (gen/vector gen-int)])
                          dedup? gen/boolean]
             (let [call (if dedup? [:call 'sort [:call 'distinct 'xs]] [:call 'sort 'xs])
                   want (realize (t/evaluate call {'xs xs}))]
               (and (= want (realize (t/evaluate (sort-model ctx (nth call 2)) {'xs xs})))
                    (= want (realize (t/evaluate (normalize ctx call) {'xs xs}))))))
         res (tc/quick-check trials p :seed seed)]
     (if (:pass? res)
       {:ok true}
       {:ok false :counterexample (get-in res [:shrunk :smallest])}))))
