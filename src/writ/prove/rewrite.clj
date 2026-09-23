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

(defn int-term?
  "Is t known to be an integer?  Literals, linear forms, counts, and
  variables typed Nat or Int.  Nothing else is trusted."
  [ctx t]
  (or (t/int-lit? t)
      (contains? #{:lin} (head t))
      (and (symbol? t) (contains? int-types (get-in ctx [:types t])))
      (and (= :call (head t)) (= 'count (second t)))))

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
    (concat facts (for [a atoms :when (nat-atom? ctx a)] {:c 0 :m {a 1}}))))

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
    (:sq :fn :cfn) true
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

(defn float-free?
  "Can this term's value hold no float?  Then two syntactically equal
  terms are =; with a NaN inside, Clojure's = says they are not."
  [ctx x]
  (cond
    (int-term? ctx x) true
    (symbol? x) (float-free-type? ctx (get-in ctx [:types x]))
    :else
    (case (head x)
      :nil true
      :lit (not (float? (second x)))
      :sq (float-free? ctx (second x))
      :enil true
      :econs (and (float-free? ctx (nth x 1)) (float-free? ctx (nth x 2)))
      :eapp (and (float-free? ctx (nth x 1)) (float-free? ctx (nth x 2)))
      :elems (float-free? ctx (second x))
      false)))

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
          (and (= a b) (float-free? ctx a)) [:lit true]
          :else nil))
      (and (int-term? ctx a) (int-term? ctx b))
      [:ieq (lin-neg-canon (lin+ (lin-of ctx a) (lin* -1 (lin-of ctx b))))]
      (and (= a b) (float-free? ctx a)) [:lit true]
      :else nil)))

;; --- computed rules --------------------------------------------------------------

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

(defn- computed
  "The computed rules: a rewrite of t, or nil."
  [ctx x]
  (case (head x)
    :call
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
        nth (when (and (<= 2 n 3) (t/int-lit? b))
              (nth-rule a (second b) (if (= 3 n) (nth args 2) ::none)))
        nil))

    :ap (let [[_ f & args] x]
          (cond
            (and (= :fn (head f)) (= (count (second f)) (count args)))
            (t/subst (nth f 2) (zipmap (second f) args))
            ;; a core fn value applied is a call of it
            (= :cfn (head f)) (into [:call (second f)] args)
            :else nil))

    :le (let [d (decide ctx x)] (when (some? d) [:lit d]))
    :ieq (let [d (decide ctx x)] (when (some? d) [:lit d]))
    nil))

;; --- normalising ------------------------------------------------------------------

(defn- out-of-fuel! []
  (throw (ex-info "out of fuel" {::fuel true})))

(defn- burn! [ctx]
  (when (neg? (swap! (:fuel ctx) dec)) (out-of-fuel!)))

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
  or a split reveals that shape.  Only the guards are normalised, never
  the branches, so a recursive call inside a branch is not unfolded here."
  [ctx body]
  (if (= :if (head body))
    (let [c (normalize ctx (nth body 1))
          tr (truthiness ctx c)]
      (cond
        (true? tr) (settled? ctx (nth body 2))
        (false? tr) (settled? ctx (nth body 3))
        (and (= :call (head c)) (= 'not (second c)))
        (settled? ctx [:if (nth c 2) (nth body 3) (nth body 2)])
        (splittable? c) (and (settled? (assume ctx c true) (nth body 2))
                             (settled? (assume ctx c false) (nth body 3)))
        :else false))
    true))

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

(defn- ih-rewrite [ctx x]
  (some (fn [{:keys [hyp lhs rhs]}]
          (when (and (= x lhs) (or (nil? hyp) (true? (truthiness ctx (normalize ctx hyp)))))
            (swap! (:used-ih ctx) inc)
            rhs))
        (:ih ctx)))

(defn match-term
  "Bindings of pattern variables `vs` that make `pat` equal to x, or nil."
  ([pat x vs] (match-term pat x vs {}))
  ([pat x vs m]
   (cond
     (nil? m) nil
     (and (symbol? pat) (contains? vs pat))
     (if (contains? m pat) (when (= (get m pat) x) m) (assoc m pat x))
     (and (vector? pat) (vector? x) (= (count pat) (count x)))
     (reduce (fn [m [p y]] (or (match-term p y vs m) (reduced nil))) m (map vector pat x))
     (= pat x) m
     :else nil)))

(declare normalize truthiness)

(defn- lemma-rewrite
  "Rewrite x by an earlier proved law: its left side matched against x,
  its hypothesis, instantiated, normalised to true here."
  [ctx x]
  (some (fn [{:keys [vars hyp lhs rhs name]}]
          (when-let [m (match-term lhs x vars)]
            (when (every? #(contains? m %) (t/vars rhs))
              (when (or (nil? hyp)
                        (let [h (t/subst hyp m)]
                          (and (every? #(not (contains? vars %)) (t/vars h))
                               (true? (truthiness ctx (normalize ctx h))))))
                (swap! (:lemmas-used ctx) conj name)
                (t/subst rhs m)))))
        (:lemmas ctx)))

(def ^:private boolean-fns
  '#{= not= not < <= > >= empty? zero? pos? neg? even? odd? nil? some? true? false?})

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

(defn- step [ctx x]
  (or (ih-rewrite ctx x)
      (lemma-rewrite ctx x)
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
    (assoc ctx :facts facts :memo (atom {}) :stuck (atom #{})))))

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
                         :fn (let [[_ ps body] x] [:fn ps (normalize ctx body)])
                         (into [(head x)] (map #(normalize ctx %)) (rest x)))]
                (if (= :if (head x))
                  ;; a boolean law's left side is often an if: an induction
                  ;; hypothesis or a lemma may still rewrite the whole of one
                  (if-let [y (and (= :if (head x*))
                                  (or (ih-rewrite ctx x*) (lemma-rewrite ctx x*)))]
                    (do (burn! ctx) (normalize ctx y))
                    x*)
                  (do (burn! ctx)
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
   :memo (atom {}) :stuck (atom #{}) :unfolded (atom #{}) :used-ih (atom 0)
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
                     (gen/tuple (gen/elements '[<= < >= > +]) sub))])))))

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
