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
    ;; every sequential value is a seq term, and nothing else is one
    [sequential-sq  [:call sequential? [:sq ?E]]        [:lit true]]
    [sequential-nil [:call sequential? [:nil]]          [:lit false]]
    [sequential-fn  [:call sequential? [:fn ?p ?b]]     [:lit false]]
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
    ;; take and drop count down with pos? and dec, as clojure.core's do,
    ;; so these hold for any count
    [take-nil      [:call take ?n [:nil]]               [:sq [:enil]]]
    [take-empty    [:call take ?n [:sq [:enil]]]        [:sq [:enil]]]
    [take-cons     [:call take ?n [:sq [:econs ?h ?E]]]
                   [:if [:call pos? ?n] [:sq [:econs ?h [:elems [:call take [:call dec ?n] [:sq ?E]]]]] [:sq [:enil]]]]
    [take-elems    [:call take ?n [:sq [:elems ?v]]]    [:call take ?n ?v]]
    [drop-nil      [:call drop ?n [:nil]]               [:sq [:enil]]]
    [drop-empty    [:call drop ?n [:sq [:enil]]]        [:sq [:enil]]]
    [drop-cons     [:call drop ?n [:sq [:econs ?h ?E]]]
                   [:if [:call pos? ?n] [:call drop [:call dec ?n] [:sq ?E]] [:sq [:econs ?h ?E]]]]
    [drop-elems    [:call drop ?n [:sq [:elems ?v]]]    [:call drop ?n ?v]]
    ;; keep is map then filter some?, in one walk
    [keep-nil      [:call keep ?f [:nil]]               [:sq [:enil]]]
    [keep-empty    [:call keep ?f [:sq [:enil]]]        [:sq [:enil]]]
    [keep-cons     [:call keep ?f [:sq [:econs ?h ?E]]]
                   [:if [:call some? [:ap ?f ?h]]
                        [:sq [:econs [:ap ?f ?h] [:elems [:call keep ?f [:sq ?E]]]]]
                        [:call keep ?f [:sq ?E]]]]
    [keep-elems    [:call keep ?f [:sq [:elems ?v]]]    [:call keep ?f ?v]]
    ;; mapcat concatenates what f gives each element
    [mapcat-nil    [:call mapcat ?f [:nil]]             [:sq [:enil]]]
    [mapcat-empty  [:call mapcat ?f [:sq [:enil]]]      [:sq [:enil]]]
    [mapcat-cons   [:call mapcat ?f [:sq [:econs ?h ?E]]]
                   [:sq [:eapp [:elems [:ap ?f ?h]] [:elems [:call mapcat ?f [:sq ?E]]]]]]
    [mapcat-elems  [:call mapcat ?f [:sq [:elems ?v]]]  [:call mapcat ?f ?v]]
    ;; reverse puts the head last
    [reverse-nil   [:call reverse [:nil]]               [:sq [:enil]]]
    [reverse-empty [:call reverse [:sq [:enil]]]        [:sq [:enil]]]
    [reverse-cons  [:call reverse [:sq [:econs ?h ?E]]]
                   [:sq [:eapp [:elems [:call reverse [:sq ?E]]] [:econs ?h [:enil]]]]]
    [reverse-elems [:call reverse [:sq [:elems ?v]]]    [:call reverse ?v]]
    ;; vec, mapv and filterv are their seq's elements; remove and not-any?
    ;; are filter and some, negated
    [vec-def       [:call vec ?x]                       [:sq [:elems ?x]]]
    [mapv-def      [:call mapv ?f ?x]                   [:call map ?f ?x]]
    [filterv-def   [:call filterv ?f ?x]                [:call filter ?f ?x]]
    [remove-def    [:call remove ?f ?x]                 [:call filter [:fn [%rm] [:call not [:ap ?f %rm]]] ?x]]
    [not-any-def   [:call not-any? ?f ?x]               [:call not [:call some ?f ?x]]]
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
              (symbol? e) (contains? #{{:writ/elems 'Nat} {:writ/elems 'Int}} (get-in ctx [:types e]))
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

(defn record-type?
  "Is ty a record, a map of keys to their types?"
  [ty]
  (and (map? ty) (seq ty) (not (contains? ty :writ/elems)) (every? keyword? (keys ty))))

(defn- term-type
  "The type of term t when its form says it: a variable's own, a list of
  a tail's elements, an element nth takes from a list (nth throws, rather
  than give anything else), a part of a Tuple, whose length is fixed, and
  a record's value at one of its keys.  nil otherwise; never from a fn's
  signature."
  [ctx t]
  (let [list-el (fn [ty] (cond (and (seq? ty) (contains? '#{List Vec} (first ty))) (second ty)
                               (and (map? ty) (:writ/elems ty)) (:writ/elems ty)
                               :else nil))]
    (cond
      (symbol? t) (get-in ctx [:types t])
      (and (= :sq (head t)) (symbol? (second t))) (some->> (get-in ctx [:types (second t)]) :writ/elems (list 'List))
      (not= :call (head t)) nil
      :else
      (let [[_ f x i] t
            ty (term-type ctx x)
            k (case f
                first (when (= 3 (count t)) 0)
                second (when (= 3 (count t)) 1)
                nth (when (and (= 4 (count t)) (t/int-lit? i)) (second i))
                nil)]
        (cond
          (and ty (seq? ty) (= 'Tuple (first ty)) k (< -1 k (dec (count ty)))) (nth ty (inc k))
          (and (= 'get f) (= 4 (count t)) (record-type? ty) (= :lit (head i)) (contains? ty (second i)))
          (get ty (second i))
          (and (= 'nth f) (= 4 (count t)) (list-el ty)) (list-el ty)
          :else nil)))))

(defn- tuple-part-type
  "The type of (first x), (second x) or (nth x k) for a term x of a Tuple
  type, or of (get x k) for a record x, or nil."
  [ctx t]
  (when (and (= :call (head t)) (contains? '#{first second nth get} (second t)))
    (term-type ctx t)))

(defn int-term?
  "Is t known to be an integer?  Literals, linear forms, counts, variables
  typed Nat or Int, and their parts of a Tuple, and a term a fact,
  hypothesis or proved lemma says is an integer?.  Nothing else is
  trusted: not even a fn's signature."
  [ctx t]
  (or (t/int-lit? t)
      (contains? #{:lin} (head t))
      (and (symbol? t) (contains? int-types (get-in ctx [:types t])))
      (contains? int-types (tuple-part-type ctx t))
      (and (= :call (head t)) (= 'count (second t)))
      (and (= :call (head t)) (= 'apply (second t)) (= [:cfn '+] (nth t 2 nil))
           (int-elems? ctx (nth t 3 nil)))
      (division? ctx t)
      (and (contains? #{:app :call} (head t)) (proved-integer? ctx t))))

(declare proved-nat?)

(defn- nat-atom? [ctx a]
  (or (and (symbol? a) (= 'Nat (get-in ctx [:types a])))
      (= 'Nat (tuple-part-type ctx a))
      (and (= :call (head a)) (= 'count (second a)))
      (and (= :app (head a)) (proved-nat? ctx a))))

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
  (let [pairs (vec (t/sort-printed first (remove (comp zero? second) m)))]
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

(defn- int-at-most?
  "Is integer a known to be at most integer b?"
  [ctx a b]
  (let [la (lin-of ctx a) lb (lin-of ctx b)]
    (and la lb (true? (decide-le ctx (lin->term (lin+ lb (lin* -1 la))))))))

(defn- bounded-by-fact
  "true when a fact bounds the comparison c, (< a x) or (<= a x) where x
  is not known to be an integer, from the same side: a <= a' and a fact
  a' <= x gives a <= x.  So it holds whatever number x is.  A strict c
  needs a strict fact: a double can round a < a' to equal."
  [ctx c]
  (when (and (= :call (head c)) (contains? '#{< <=} (second c)) (= 4 (count c)))
    (let [[_ op a x] c]
      (some (fn [[f v]]
              (when (and (true? v) (= :call (head f)) (contains? '#{< <=} (second f)) (= 4 (count f))
                         (or (= op '<=) (= (second f) '<)))
                (let [[_ _ a' x'] f]
                  (or (and (= x x') (not= a a') (int-at-most? ctx a a'))
                      (and (= a a') (not= x x') (int-at-most? ctx x' x))))))
            (:facts ctx)))))

(defn decide
  "The truth of condition c under ctx, or nil when it is open."
  [ctx c]
  (cond
    (= :le (head c)) (let [f (get (:facts ctx) c)] (if (some? f) f (decide-le ctx (second c))))
    (= :ieq (head c)) (decide-ieq ctx (second c))
    (contains? (:facts ctx) c) (get (:facts ctx) c)
    (bounded-by-fact ctx c) true
    :else nil))

(def ^:private seq-makers
  "clojure.core fns that always return a seq or vector object, which is
  truthy whatever it holds.  A lazy one is truthy before it is realised,
  so its elements must not be computed to decide it."
  '#{filter map concat rest cons list vector vec mapcat keep take drop reverse range
     mapv filterv subvec hash-map hash-set assoc})

(def ^:private number-makers
  "clojure.core fns that return a number or throw: never nil or false."
  '#{inc dec + - * count quot rem mod max min abs})

(defn- nil-fact
  "false when a fact says c is nil: (nil? c), or (some? c) false."
  [ctx c]
  (when (or (true? (get (:facts ctx) [:call 'nil? c]))
            (false? (get (:facts ctx) [:call 'some? c])))
    false))

(defn- truthy-type?
  "Is every value of ty truthy: never nil, never false?  A number, a
  string, a vector, a set, a map, a record or a datatype's value; not a
  Bool, a (List T), which may be nil, an (Opt T) or an Any."
  [ctx ty]
  (boolean
    (or (contains? '#{Nat Int String Char Keyword Symbol Float Double Float! Double!} ty)
        (and (seq? ty) (contains? '#{Vec Set Map Tuple} (first ty)))
        (record-type? ty)
        (and (symbol? ty) (map? (get-in ctx [:tenv ty])) (:ctors (get-in ctx [:tenv ty]))
             (not (:tvar (get-in ctx [:tenv ty]))))
        (and (seq? ty) (symbol? (first ty)) (:ctors (get-in ctx [:tenv (first ty)]))))))

(declare truthiness*)

(defn truthiness
  "true / false for a term whose truthiness is settled, else nil.  An if
  whose branches agree has their truthiness without its test being run:
  a lazy seq's elements can hide behind such an if, and computing them
  could throw where the seq, unrealised, would not."
  [ctx c]
  (if (truthy-type? ctx (term-type ctx c))
    true
    (truthiness* ctx c)))

(defn- truthiness* [ctx c]
  (case (head c)
    :nil false
    :lit (not (false? (second c)))
    (:sq :fn :cfn :dfn) true
    :if (let [a (truthiness ctx (nth c 2)) b (truthiness ctx (nth c 3))]
          (when (and (some? a) (= a b)) a))
    :call (if (or (contains? seq-makers (second c)) (contains? number-makers (second c))
                  (int-term? ctx c))
            true
            (let [d (decide ctx c)] (if (some? d) d (nil-fact ctx c))))
    ;; a call of a definition that a fact or a law says is an integer
    :app (if (int-term? ctx c)
           true
           (let [d (decide ctx c)] (if (some? d) d (nil-fact ctx c))))
    (let [d (decide ctx c)] (if (some? d) d (nil-fact ctx c)))))

;; --- equality ------------------------------------------------------------------

(def ^:private float-free-types
  "The types whose values hold no NaN.  That is all of them: writ's types
  range over values without NaN, as its generators do (a Double or an Any
  is never ##NaN), so a law over Any says nothing about a NaN.  A NaN the
  code computes, (/ 0.0 0.0), is another matter: float-free? keeps to
  terms that only pick and arrange parts of the law's values."
  '#{Nat Int Bool String Keyword Symbol Char Unit Any Float Double})

(defn- float-free-type?
  "seen: the data types already being checked; a field of one of them is
  float-free if the rest of the type is."
  ([ctx ty] (float-free-type? ctx ty #{}))
  ([ctx ty seen]
   (cond
     (contains? float-free-types ty) true
     ;; a type variable ranges over the values of some type
     (and (symbol? ty) (:tvar (get-in ctx [:tenv ty]))) true
     (contains? seen ty) true
     (and (seq? ty) (contains? '#{List Vec} (first ty))) (float-free-type? ctx (second ty) seen)
     (and (seq? ty) (contains? '#{Map Set Tuple Opt} (first ty))) (every? #(float-free-type? ctx % seen) (rest ty))
     (record-type? ty) (every? #(float-free-type? ctx % seen) (vals ty))
     (and (map? ty) (:writ/elems ty)) (float-free-type? ctx (:writ/elems ty) seen)
     (and (symbol? ty) (get-in ctx [:tenv ty]))
     (every? (fn [[_ c]] (every? #(float-free-type? ctx % (conj seen ty)) (:fields c)))
             (:ctors (get-in ctx [:tenv ty])))
     :else false)))

(declare boolean-term? has-type?)

(def ^:private selecting-fns
  "clojure.core fns whose value is made of parts of their data arguments
  and nothing else: no float in, no float out.  A fn argument only picks
  which parts."
  '#{filter remove concat list vector vec cons rest next seq take drop reverse
     sort distinct butlast first second last nth subvec filterv
     get keys vals hash-map assoc dissoc merge})

(defn float-free?
  "Can this term's value hold no NaN?  Then two syntactically equal terms
  are =; with a NaN inside, Clojure's = says they are not.  Only the
  law's values and what is picked from them qualify, and literals other
  than ##NaN: arithmetic on floats can make a NaN of none.  A value
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
         :lit (not (and (float? (second x)) (Double/isNaN (second x))))
         :sq (ff? (second x))
         :enil true
         :econs (and (ff? (nth x 1)) (ff? (nth x 2)))
         :eapp (and (ff? (nth x 1)) (ff? (nth x 2)))
         :elems (ff? (second x))
         :if (and (ff? (nth x 2)) (ff? (nth x 3)))
         :call (let [[_ f & args] x]
                 (cond
                   ;; an index or a count only picks which parts: a NaN one
                   ;; would throw
                   (contains? '#{nth get subvec} f) (ff? (first args))
                   (contains? '#{take drop} f) (ff? (second args))
                   (contains? selecting-fns f)
                   (every? ff? (remove #(contains? #{:fn :cfn :dfn} (head %)) args))
                   ;; what a fn literal makes of float-free elements
                   (and (contains? '#{map mapcat keep} f) (= 2 (count args)) (= :fn (head (first args)))
                        (= 1 (count (second (first args)))))
                   (let [[[_ ps body] coll] args]
                     (and (ff? coll) (float-free? ctx body (into env ps) seen)))
                   (= 'range f) (every? ff? args)
                   ;; a picking core fn mapped over them
                   (and (contains? '#{map mapcat keep} f) (= 2 (count args)) (= :cfn (head (first args)))
                        (contains? selecting-fns (second (first args))))
                   (ff? (second args))
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
                (if (:params d)
                  (and (= (count args) (count (:params d)))
                       (every? ff? args)
                       (or (contains? seen f)
                           (float-free? ctx (:body d) (set (:params d)) (conj seen f))))
                  ;; a fn with no definition to read -- one the spec assumes a
                  ;; signature for -- by its contract: a value of a scalar
                  ;; type other than a float
                  (boolean (some #(has-type? ctx % x) '[String Keyword Symbol Char Bool Int]))))
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

(defn- nan-lit? [t] (and (= :lit (head t)) (float? (second t)) (Double/isNaN (second t))))

(defn- equality [ctx a b]
  (let [ha (head a) hb (head b)]
    (cond
      ;; nothing is = to NaN, NaN included
      (or (nan-lit? a) (nan-lit? b)) [:lit false]
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
      ;; = is symmetric: of two other terms, the one that prints first goes
      ;; first, so (= m n) and (= n m) are one term, and a fact of one
      ;; decides the other
      (and (not= :lit ha) (not= :lit hb) (pos? (compare (pr-str a) (pr-str b))))
      [:call '= b a]
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
        (set? v) (let [ts (map value-term (t/sort-printed v))] (when (every? some? ts) (into [:call 'hash-set] ts)))
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

;; --- maps on literal keys ------------------------------------------------------
;; A lookup through an assoc or a dissoc on a literal key is decided by the
;; key: the same key is the value set (or gone), another key looks further
;; in.  Only keys = compares exactly, so no NaN key and no float; on a
;; value that is not a map these throw, and a rule holds where its left
;; side returns.

(defn- exact-key? [k] (and (= :lit (head k)) (exact-scalar? (second k))))

(defn- map-entries
  "The entries of a hash-map term on exact literal keys, last one winning,
  as [[k v] ...] in the order they print, or nil."
  [x]
  (when (and (= :call (head x)) (= 'hash-map (second x)) (even? (count (drop 2 x))))
    (let [kvs (partition 2 (drop 2 x))]
      (when (every? (comp exact-key? first) kvs)
        (sort-by (comp pr-str second first)
                 (vals (reduce (fn [m [k v]] (assoc m (second k) [k v])) {} kvs)))))))

(defn- entries->term [es] (into [:call 'hash-map] (mapcat identity es)))

(defn- map-lookup
  "(get m k d) on an exact key k, when m's make-up decides it: `found` of
  the value when k is there, `absent` when it is not, or a rewrite into m's
  own lookup.  nil when it does not."
  [m k found absent further]
  (cond
    (= t/tnil m) absent
    (and (= :call (head m)) (= 'assoc (second m)) (= 5 (count m)) (exact-key? (nth m 3)))
    (if (= k (nth m 3)) (found (nth m 4)) (further (nth m 2)))
    (and (= :call (head m)) (= 'dissoc (second m)) (= 4 (count m)) (exact-key? (nth m 3)))
    (if (= k (nth m 3)) absent (further (nth m 2)))
    :else
    (when-let [es (map-entries m)]
      (if-let [[_ v] (first (filter #(= k (first %)) es))] (found v) absent))))

(defn- non-nil-map?
  "Is term m a map, never nil: built by hash-map or assoc, a dissoc of
  one, or of a record or Map type?"
  [ctx m]
  (or (and (= :call (head m)) (contains? '#{hash-map assoc} (second m)))
      (and (= :call (head m)) (= 'dissoc (second m)) (non-nil-map? ctx (nth m 2)))
      (let [ty (term-type ctx m)]
        (or (record-type? ty) (and (seq? ty) (= 'Map (first ty)))))))

(defn- map-rule
  "get, contains?, assoc and dissoc on literal keys; an assoc or dissoc of
  several keys is one after another."
  [ctx f args]
  (let [n (count args) [m k] args]
    (case f
      get (when (and (<= 2 n 3) (exact-key? k))
            (map-lookup m k identity (if (= 3 n) (nth args 2) t/tnil)
                        #(into [:call 'get % k] (drop 2 args))))
      contains? (when (and (= 2 n) (exact-key? k))
                  (map-lookup m k (constantly [:lit true]) [:lit false] #(vector :call 'contains? % k)))
      assoc (cond
              (and (< 3 n) (odd? n))
              (reduce (fn [acc [k v]] [:call 'assoc acc k v]) m (partition 2 (rest args)))
              (and (= 3 n) (exact-key? k))
              (cond
                ;; a second assoc of a key replaces the first
                (and (= :call (head m)) (= 'assoc (second m)) (= 5 (count m)) (= k (nth m 3)))
                [:call 'assoc (nth m 2) k (nth args 2)]
                (map-entries m)
                (entries->term (sort-by (comp pr-str second first)
                                        (conj (remove #(= k (first %)) (map-entries m)) [k (nth args 2)])))
                :else nil)
              :else nil)
      ;; a map is not a seq, and nor is nil
      seq? (when (and (= 1 n) (or (= t/tnil m) (non-nil-map? ctx m))) [:lit false])
      dissoc (cond
               (< 2 n) (reduce (fn [acc k] [:call 'dissoc acc k]) m (rest args))
               (and (= 2 n) (exact-key? k))
               (cond
                 (= t/tnil m) t/tnil
                 (and (= :call (head m)) (= 'assoc (second m)) (= 5 (count m)) (exact-key? (nth m 3)))
                 (cond
                   ;; on nil, the assoc makes a map and the dissoc leaves it
                   ;; empty, where a dissoc of nil is nil
                   (not= k (nth m 3)) [:call 'assoc [:call 'dissoc (nth m 2) k] (nth m 3) (nth m 4)]
                   (non-nil-map? ctx (nth m 2)) [:call 'dissoc (nth m 2) k]
                   :else nil)
                 (and (= :call (head m)) (= 'dissoc (second m)) (= 4 (count m)) (= k (nth m 3)))
                 m
                 (map-entries m) (entries->term (remove #(= k (first %)) (map-entries m)))
                 :else nil)
               :else nil)
      nil)))

(defn- computed
  "The computed rules: a rewrite of t, or nil."
  [ctx x]
  (case (head x)
    :call
    (or
     (when-not (= 'hash-set (second x)) (ground-call x))
     (map-rule ctx (second x) (drop 2 x))
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
        ;; writ's same is = with NaN the same as NaN: every value is the
        ;; same as itself, and values that hold no NaN are same when =
        writ.prove.term/same
        (when (= 2 n)
          (let [ea (when (= :sq (head a)) (second a)) eb (when (= :sq (head b)) (second b))
                va (closed-value a) vb (closed-value b)]
            (cond
              (= a b) [:lit true]
              (and (not= ::none va) (not= ::none vb)) [:lit (t/same va vb)]
              (and (float-free? ctx a) (float-free? ctx b)) [:call '= a b]
              (and (= :econs (head ea)) (= :econs (head eb)))
              [:if [:call 'writ.prove.term/same (nth ea 1) (nth eb 1)]
               [:call 'writ.prove.term/same [:sq (nth ea 2)] [:sq (nth eb 2)]]
               [:lit false]]
              (and (= :enil (head ea)) (= :enil (head eb))) [:lit true]
              (or (and (= :enil (head ea)) (= :econs (head eb))) (and (= :econs (head ea)) (= :enil (head eb))))
              [:lit false]
              :else nil)))
        ;; max and min are comparisons on integers; with a NaN in, the
        ;; answer is NaN whichever way > goes, so only integers
        max (when (and (= 2 n) (int-term? ctx a) (int-term? ctx b)) [:if [:call '> a b] a b])
        min (when (and (= 2 n) (int-term? ctx a) (int-term? ctx b)) [:if [:call '< a b] a b])
        ;; whether some element is in a set does not depend on their order:
        ;; a set applied never throws, so some cannot stop short of a throw
        not (cond
              (= :le (head a)) [:le (lin->term (lin+ (lin* -1 (lin-of ctx (second a))) {:c -1 :m {}}))]
              (and (= :call (head a)) (= 'some (second a)) (= 4 (count a))
                   (= :call (head (nth a 2))) (= 'hash-set (second (nth a 2)))
                   (= :call (head (nth a 3))) (= 'reverse (second (nth a 3))) (= 3 (count (nth a 3))))
              [:call 'not [:call 'some (nth a 2) (nth (nth a 3) 2)]]
              :else (let [tr (truthiness ctx a)] (when (some? tr) [:lit (not tr)])))
        ;; (keep (fn [x] (when p v)) xs), v never nil, keeps v for each x
        ;; p takes: the map of v over the filter of p, as a for with :when is
        keep (when (= 2 n)
               (let [[f xs] args]
                 (when (and (= :fn (head f)) (= 1 (count (second f))) (= :if (head (nth f 2))))
                   (let [[_ ps [_ p v w]] f]
                     (cond
                       (and (= t/tnil w) (true? (truthiness ctx v)))
                       [:call 'map [:fn ps v] [:call 'filter [:fn ps p] xs]]
                       (and (= t/tnil v) (true? (truthiness ctx w)))
                       [:call 'map [:fn ps w] [:call 'filter [:fn ps [:call 'not p]] xs]]
                       :else nil)))))
        ;; a fn value is a fn; data is not
        fn? (when (= 1 n)
              (cond (contains? #{:fn :cfn :dfn} (head a)) [:lit true]
                    (or (int-term? ctx a) (contains? #{:lit :nil :sq} (head a))
                        (and (= :call (head a)) (contains? '#{hash-map hash-set assoc} (second a))))
                    [:lit false]
                    :else nil))
        ;; an integer is a number, and a seq, nil or a fn is not
        number? (when (= 1 n)
                  (cond (int-term? ctx a) [:lit true]
                        (= :lit (head a)) [:lit (number? (second a))]
                        (contains? #{:sq :nil :fn :cfn :dfn} (head a)) [:lit false]
                        :else nil))
        ;; a truthy value is not nil, and a value that is neither nil nor
        ;; false is truthy
        some? (when (= 1 n) (if (true? (truthiness ctx a)) [:lit true] (when (= t/tnil a) [:lit false])))
        nil? (when (= 1 n) (if (true? (truthiness ctx a)) [:lit false] (when (= t/tnil a) [:lit true])))
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
        nth (cond
              (and (<= 2 n 3) (t/int-lit? b))
              (nth-rule a (second b) (if (= 3 n) (nth args 2) ::none))
              ;; an integer index into a known head: the head at 0, else
              ;; one less into the tail.  At a negative index nth throws,
              ;; so the test can be (<= i 0), and the other case says i >= 1
              (and (<= 2 n 3) (int-term? ctx b) (= :sq (head a)) (= :econs (head (second a))))
              (let [[_ h e] (second a)]
                [:if [:call '<= b [:lit 0]] h
                 (into [:call 'nth [:sq e] [:call 'dec b]] (drop 2 args))])
              :else nil)
        ;; (subvec v i j) is j - i elements from i on, on integer indexes;
        ;; it throws where those would not fit, and a rule holds where its
        ;; left side returns
        subvec (when (and (every? #(int-term? ctx %) (rest args)) (<= 2 n 3))
                 (if (= 2 n)
                   [:call 'drop b a]
                   [:call 'take [:call '- (nth args 2) b] [:call 'drop b a]]))
        ;; (range a b) on integers, one element at a time, once the facts
        ;; say whether a < b: open, it stays, or it would unfold for ever
        range (cond
                (and (= 1 n) (int-term? ctx a)) [:call 'range [:lit 0] a]
                (and (= 2 n) (int-term? ctx a) (int-term? ctx b))
                (case (decide ctx (lt ctx a b))
                  true [:sq [:econs a [:elems [:call 'range [:call 'inc a] b]]]]
                  false [:sq t/enil]
                  nil)
                :else nil)
        nil)))

    :ap (let [[_ f & args] x]
          (cond
            (and (= :fn (head f)) (= (count (second f)) (count args)))
            (t/subst (nth f 2) (zipmap (second f) args))
            ;; a core fn value applied is a call of it, and a defn's an app
            (= :cfn (head f)) (into [:call (second f)] args)
            (= :dfn (head f)) (into [:app (second f)] args)
            ;; a set applied is the member equal to its argument, or nil
            (and (= :call (head f)) (= 'hash-set (second f)) (= 1 (count args)))
            (reduce (fn [else e] [:if [:call '= (first args) e] e else]) t/tnil (reverse (drop 2 f)))
            :else nil))

    :le (let [d (decide ctx x)] (when (some? d) [:lit d]))
    :ieq (let [d (decide ctx x)] (when (some? d) [:lit d]))
    ;; the elements of a value that is always a seq, as a seq, are it
    :sq (let [e (second x)]
          (when (and (= :elems (head e)) (= :call (head (second e)))
                     (contains? seq-makers (second (second e)))
                     (not (contains? '#{hash-map hash-set assoc} (second (second e)))))
            (second e)))
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
     (some-> (:burned ctx) (swap! inc))
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

(defn- shape-test?
  "Does condition c read the shape of a variable's value -- (seq xs),
  (first (rest t)), (nth v 0) -- which a case split or an induction
  could reveal?  An element at an index that is not a literal,
  (= k (nth xs i)), is no shape: no split on xs decides it."
  [c]
  (some (fn [x]
          (and (= :call (head x)) (some? (nth x 2 nil)) (seq (t/vars (nth x 2)))
               (or (contains? '#{seq first rest next empty? count second last
                                 sequential? vector? map? nil? some?}
                              (second x))
                   (and (= 'nth (second x)) (t/int-lit? (nth x 3 nil))))))
        (t/subterms c)))

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
  own guards settle, and nor is a test no split could decide, such as
  an element at an index.  Only the guards are normalised, never the
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
         (and decided? (or (some #(= :app (head %)) (t/subterms c)) (not (shape-test? c))))
         (and (settled? ctx (nth body 2) true) (settled? ctx (nth body 3) true))
         :else false))
     true)))

(defn- unfold
  "The body of definition call x, when it should be unfolded.  A recursive
  definition whose first guard is open is unfolded one level: each call
  of itself in the body is held, and a held call is unfolded only once
  the facts decide its own first guard -- or (f (inc i)) would unfold
  into (f (+ i 2)) and on until the fuel ran out.  A split on a guard
  decides it, and the next level opens then."
  [ctx x]
  (let [[_ f & args] x
        d (get-in ctx [:defs f])]
    (when (and d (= (count (:params d)) (count args))
               (not (contains? @(:stuck ctx) x)))
      (let [body (t/subst (:body d) (zipmap (:params d) args))
            open? (delay (and (= :if (head body))
                              (nil? (truthiness ctx (normalize ctx (nth body 1))))))]
        (when-not (and (:recursive? d) (contains? @(:held ctx) x) @open?)
          (burn! ctx)
          (if-not (:recursive? d)
            (do (swap! (:unfolded ctx) conj f) body)
            (if (settled? ctx body)
              (do (swap! (:unfolded ctx) conj f)
                  (when @open?
                    (swap! (:held ctx) into
                           (for [y (t/subterms body)
                                 :when (and (= :app (head y)) (= f (second y)))]
                             (into [:app f] (map #(normalize ctx %)) (drop 2 y)))))
                  body)
              (do (swap! (:stuck ctx) conj x) nil))))))))

(defn hold-calls!
  "Hold, in ctx, each call of a recursive definition in t: normalised, it
  stays folded until the facts decide its first guard.  An induction
  hypothesis about (f (inc i)) rewrites only a goal where that call is
  folded, as it is under an unfolding of (f i)."
  [ctx t]
  (swap! (:held ctx) into
         (for [y (t/subterms t)
               :when (and (= :app (head y)) (:recursive? (get-in ctx [:defs (second y)])))]
           (into [:app (second y)] (map #(normalize ctx %)) (drop 2 y))))
  ctx)

(declare match-term)

(defn- loops?
  "Would rewriting x to y only put x back inside a bigger term?"
  [x y]
  (and (not= x y) (some #(= x %) (t/subterms y))))

(def ^:private sublist-fns
  "clojure.core fns whose value is a seq of some of their list's elements,
  never nil: (fn ... xs), xs last."
  '#{drop take rest filter remove reverse filterv vec distinct})

(defn- elem-type
  "The element type of a list term, when its form says it: a variable of a
  list type or a tail of one, or a sublist of such a term.  [T non-nil?]."
  [ctx u]
  (let [ty (if (symbol? u) (get-in ctx [:types u]))]
    (cond
      (and (seq? ty) (contains? '#{List Vec} (first ty))) [(second ty) (= 'Vec (first ty))]
      (and (= :sq (head u)) (symbol? (second u)) (:writ/elems (get-in ctx [:types (second u)])))
      [(:writ/elems (get-in ctx [:types (second u)])) true]
      (and (= :call (head u)) (contains? sublist-fns (second u)) (<= 3 (count u)))
      (when-let [[el] (elem-type ctx (last u))] [el true])
      :else nil)))

(defn has-type?
  "Is term u known to be of type ty?  A variable of that type is; an
  integer term is an Int, and a Nat when it is not negative; anything else
  is when the type's recognizer, applied to it, rewrites to true.  A type
  with no recognizer (a set, a map) takes only a variable of its own."
  [ctx ty u]
  (let [el (fn [t] (when (and (seq? t) (contains? '#{List Vec} (first t))) (second t)))]
    (boolean
      (or (= ty (get-in ctx [:types u]))
          (and (= :sq (head u)) (symbol? (second u)) (el ty)
               (= {:writ/elems (el ty)} (get-in ctx [:types (second u)])))
          ;; a sublist of a list of its elements: never nil, so a Vec too
          (and (el ty) (= :call (head u))
               (let [[t non-nil?] (elem-type ctx u)]
                 (and (= t (el ty)) (or non-nil? (= 'List (first ty))))))
          (case ty
            Int (int-term? ctx u)
            Nat (and (int-term? ctx u)
                     (true? (truthiness ctx (normalize ctx [:call '<= [:lit 0] u]))))
            (let [c (get-in ctx [:recognizers :checks ty])]
              (cond (= :any c) true
                    (nil? c) false
                    :else (true? (truthiness ctx (normalize ctx (t/subst c {'%x u})))))))))))

(defn- typed?
  "Do the terms bindings m give a rule's variables have the variables'
  types?"
  [ctx types m]
  (every? (fn [[v ty]] (or (not (contains? m v)) (has-type? ctx ty (get m v)))) types))

(defn- recognizer-rule
  "A recognizer on a variable of its type is true.  A list recognizer on a
  concatenation is its parts'; on the elements of a value, the value's
  (nil being the empty list)."
  [ctx x]
  (when (and (= :app (head x)) (= 3 (count x)))
    (let [r (second x) u (nth x 2)
          ty (some (fn [[ty n]] (when (= n r) ty)) (get-in ctx [:recognizers :names]))]
      (cond
        (and ty (or (and (symbol? u) (= ty (get-in ctx [:types u])))
                    (and (= :sq (head u)) (symbol? (second u)) (seq? ty)
                         (contains? '#{List Vec} (first ty))
                         (= {:writ/elems (second ty)} (get-in ctx [:types (second u)])))))
        [:lit true]
        (and (contains? (get-in ctx [:recognizers :lists]) r) (= :sq (head u)))
        (let [e (second u)]
          (case (head e)
            :eapp [:if [:app r [:sq (nth e 1)]] [:app r [:sq (nth e 2)]] [:lit false]]
            :elems [:if [:call '= (second e) t/tnil] [:lit true] [:app r (second e)]]
            nil))
        :else nil))))

(defn- ih-rewrite
  "Rewrite x by an induction hypothesis.  One with free variables (its
  law quantified over them as well) matches x as a pattern, and holds
  only for their declared types, which its hypothesis states."
  [ctx x]
  (some (fn [{:keys [hyp lhs rhs vars types]}]
          ;; a hypothesis whose left side is a bare variable would match
          ;; every term; it has nothing to rewrite
          (when-let [m (when-not (symbol? lhs)
                         (if (seq vars)
                           (let [m (match-term lhs x vars)] (when (and m (typed? ctx types m)) m))
                           (when (= x lhs) {})))]
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
     (or (reduce (fn [m [p y]] (or (match-term p y vs m) (reduced nil))) m (map vector pat x))
         ;; = is symmetric, and a literal is put second, so (= ?id (f x))
         ;; is also (= (f x) 0)
         (when (and (= :call (head pat)) (= '= (second pat)) (= 4 (count pat))
                    (= :call (head x)) (= '= (second x)))
           (some->> m (match-term (nth pat 3) (nth x 2) vs) (match-term (nth pat 2) (nth x 3) vs))))
     (= pat x) m
     :else nil)))

(declare normalize truthiness ih-rewrite lemma-rewrite)

(def ^:dynamic *provisional*
  "True while a question about a term is being worked out with a
  provisional answer to it in place, to stop a loop: nothing worked out
  then is memoised, since it may rest on that answer."
  false)

(defn- provisionally
  "(f), with k's answer taken to be false in memo while it runs.  The
  answer is kept only when no outer question was open, for then it rests
  on nothing provisional."
  [memo k f]
  (let [outer *provisional*
        _ (some-> memo (swap! assoc k false))
        r (binding [*provisional* true] (f))]
    (if outer
      (some-> memo (swap! dissoc k))
      (some-> memo (swap! assoc k r)))
    r))

(defn- proved-integer?
  "Does a fact, an induction hypothesis or a proved lemma say (integer? t)?"
  [ctx t]
  (let [memo (:int-memo ctx)
        hit (some-> memo deref (get t))]
    (if (some? hit)
      hit
      (let [q [:call 'integer? t]]
        (provisionally memo t
          #(boolean (or (true? (get (:facts ctx) q))
                        (= [:lit true] (ih-rewrite ctx q))
                        (= [:lit true] (lemma-rewrite ctx q)))))))))

(defn- proved-nat?
  "Does a proved contract or law say (<= 0 t), its hypothesis holding
  here?  A contract's rule is kept as written, (<= 0 (f ?x)) to true, so
  it is read here, where t is an atom of a linear form, not by
  rewriting."
  [ctx t]
  (let [memo (:int-memo ctx)
        k [:nat t]
        hit (some-> memo deref (get k))]
    (if (some? hit)
      hit
      (provisionally memo k
        #(boolean
                (some (fn [{:keys [vars hyp lhs rhs name types]}]
                        (when (and (= [:lit true] rhs) (= :call (head lhs))
                                   (= '<= (second lhs)) (= [:lit 0] (nth lhs 2 nil)) (= 4 (count lhs)))
                          (when-let [m (match-term (nth lhs 3) t vars)]
                            ;; a law's hypothesis must hold here too
                            (when (and (typed? ctx types m)
                                       (or (nil? hyp) (true? (truthiness ctx (normalize ctx (t/subst hyp m))))))
                              (swap! (:lemmas-used ctx) conj name)
                              true))))
                      (:lemmas ctx)))))))

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
        facts (t/sort-printed (for [[f v] (:facts ctx) :when (true? v)] f))]
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
  the hypothesis the left side does not bind is bound from the facts.
  The law holds only at its own types, so each term its variables take
  must be shown to be of the variable's type."
  [ctx x]
  (some (fn [{:keys [vars hyp lhs rhs name types]}]
          (when-let [m0 (match-term lhs x vars)]
            (some (fn [m]
                    (when (and (every? #(contains? m %) (t/vars rhs)) (typed? ctx types m))
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
  '#{writ.prove.term/same number? fn? = not= not < <= > >= empty? zero? pos? neg? even? odd? nil? some? true? false? every? boolean})

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

(defn- strict
  "[:bottom] for a call, or a fn value applied, with an argument that
  throws: Clojure evaluates every argument before the call.  Not for a
  seq's elements, which a lazy seq may never compute."
  [x]
  (when (and (contains? #{:call :app :ap :le :ieq} (head x))
             (some #(= [:bottom] %) (if (= :ap (head x)) (rest x) (drop (if (contains? #{:le :ieq} (head x)) 1 2) x))))
    [:bottom]))

(defn- step [ctx x]
  (or (strict x)
      (ih-rewrite ctx x)
      (lemma-rewrite ctx x)
      (lift-if x)
      (when (and (contains? (:facts ctx) x) (not (contains? #{:le :ieq} (head x)))
                 (boolean-term? x) (boolean? (get (:facts ctx) x)))
        [:lit (get (:facts ctx) x)])
      (apply-patterns (get @indexed (rule-key x)) x)
      (computed ctx x)
      (recognizer-rule ctx x)
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
                                 (= [:bottom] c) c
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
                                   ps* (canonical-params ps body)
                                   ;; a fact that names a parameter is about
                                   ;; some other value of that name: the body
                                   ;; must not read it as about its own
                                   bound (set ps*)
                                   ctx* (if (some #(some bound (t/vars (key %))) (:facts ctx))
                                          (assoc ctx :facts (into {} (remove #(some bound (t/vars (key %)))) (:facts ctx))
                                                 :memo (atom {}) :stuck (atom #{}) :int-memo (atom {}))
                                          ctx)]
                               [:fn ps* (normalize ctx* (t/subst body (zipmap ps ps*)))])
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
      (when-not *provisional* (swap! (:memo ctx) assoc x r))
      r)))

(defn context
  "A fresh normalising context.  defs: name -> {:params :body :recursive?};
  types: variable -> type; tenv: data declarations."
  [{:keys [defs types tenv facts ih fuel lemmas lemmas-used recognizers burned unfolded]}]
  {:defs (or defs {}) :types (or types {}) :tenv (or tenv {})
   :recognizers (or recognizers {})
   :facts (or facts {}) :ih (or ih []) :lemmas (or lemmas [])
   :lemmas-used (or lemmas-used (atom #{}))
   :memo (atom {}) :stuck (atom #{}) :unfolded (or unfolded (atom #{})) :used-ih (atom 0) :int-memo (atom {})
   :held (atom #{})
   ;; every rewrite of an attempt, across its contexts, for its telemetry
   :burned burned
   :fuel (atom (or fuel 20000))})

;; --- checking the rules against the runtime ----------------------------------------

(def ^:private sample-fns
  [[:fn '[p] [:call 'inc 'p]]
   [:fn '[p] [:call 'odd? 'p]]
   [:fn '[p] [:call '< 'p [:lit 3]]]
   [:fn '[p] [:call 'list 'p 'p]]])

(def ^:private gen-int (gen/choose -5 5))

(def ^:private gen-value
  ;; a NaN now and then, alone and inside a seq: a rule must hold for them too
  (gen/frequency [[1 (gen/return nil)]
                  [3 gen-int]
                  [1 (gen/return ##NaN)]
                  [3 (gen/one-of [(gen/list gen-int) (gen/vector gen-int)])]
                  [1 (gen/list (gen/one-of [gen-int (gen/return ##NaN)]))]
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
                    ;; compared with same: a NaN on both sides is the same value
                    (let [r (returns #(t/evaluate (fill rhs)))]
                      (and r (t/same (second l) (second r))))))))
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
                     (gen/tuple (gen/elements '[cons concat list = writ.prove.term/same]) sub sub))
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
                     (and n (t/same (second o) (second n)))))))
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
