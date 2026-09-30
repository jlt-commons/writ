(ns writ.symbolic-test
  "Symbolic evaluation agrees with running the code: for concrete inputs,
  the formula for (= (f x) out) holds exactly when f returns out."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.java.io]
            [writ.book]
            [writ.prove :as prover]
            [writ.prove.symbolic :as sym]
            [writ.spec :as spec]
            [clojure.string :as str]))

(require 'writ.spec-demo.shapes 'writ.spec-demo.signal 'writ.spec-demo.court)

(defn- defs-of [ns-sym file]
  (first (prover/definitions [[ns-sym (writ.book/read-forms (clojure.java.io/resource file))]])))

(def ^:private tenv
  {'Shape {:arity 0 :params [] :ctors {'Square {:fields ['Int]}
                                       'Rect {:fields ['Int 'Int]}
                                       'Dot {:fields []}}}
   'Key {:arity 0 :params [] :ctors {'Idle {:fields []} 'Up {:fields []} 'Down {:fields []}}}})

(defn- term-of
  "The term for a value: a literal, a list or a set of them."
  [v]
  (cond (sequential? v) [:sq (reduce (fn [e x] [:econs (term-of x) e]) [:enil] (reverse v))]
        (set? v) (into [:call 'hash-set] (map term-of v))
        :else [:lit v]))

(defn- check [defs types f args envs]
  (doseq [env envs]
    (let [opts {:types types :defs defs :tenv tenv}
          actual (try (apply (resolve f) (map env args)) (catch Throwable _ ::threw))
          call (into [:app f] args)]
      (when-not (= ::threw actual)
        (is (true? (sym/agrees? opts [:call '= call (term-of actual)] env))
            (str f " at " env " is " (pr-str actual))))
      (is (true? (sym/agrees? opts [:call '= call [:lit :not-a-result]] env))
          (str f " at " env " is not :not-a-result")))))

(deftest data-with-fields-and-defaults
  (let [defs (defs-of 'writ.spec-demo.shapes "writ/spec_demo/shapes.clj")
        shapes (for [a [-3 0 2 7] b [-1 5]] [[:Square a] [:Rect a b] [:Dot]])]
    (check defs '{s Shape} 'writ.spec-demo.shapes/perimeter '[s]
           (for [s (distinct (apply concat shapes))] {'s s}))
    (check defs '{s Shape} 'writ.spec-demo.shapes/grow '[s]
           (for [s (distinct (apply concat shapes))] {'s s}))))

(deftest branches-and-division
  (let [defs (defs-of 'writ.spec-demo.shapes "writ/spec_demo/shapes.clj")]
    (check defs '{n Int} 'writ.spec-demo.shapes/bucket '[n]
           (for [n [-17 -1 0 1 5 9 10 11 99 -100]] {'n n}))))

(deftest nth-with-a-default-on-a-tuple
  (let [defs (defs-of 'writ.spec-demo.shapes "writ/spec_demo/shapes.clj")]
    (check defs '{xs (Tuple Int Keyword Int) i Int} 'writ.spec-demo.shapes/pick '[xs i]
           (for [i [-1 0 1 2 3 7]] {'xs [4 :k -2] 'i i}))))

(deftest the-demos-agree
  (let [defs (defs-of 'writ.spec-demo.signal "writ/spec_demo/signal.clj")]
    (check defs '{l (Tuple Keyword Nat)} 'writ.spec-demo.signal/tick '[l]
           (for [p [:Green :Yellow :Red :Blue] t [0 4 5 29 30 31]] {'l [p t]})))
  (let [defs (defs-of 'writ.spec-demo.court "writ/spec_demo/court.clj")]
    (check defs '{y Int k Key} 'writ.spec-demo.court/move '[y k]
           (for [y [-9 0 1 36 37 38 99] k [[:Up] [:Down] [:Idle]]] {'y y 'k k}))))

(deftest outside-is-said-not-guessed
  (testing "a product of two unknowns is not linear"
    (let [defs (defs-of 'writ.spec-demo.shapes "writ/spec_demo/shapes.clj")]
      (is (= :outside (sym/agrees? {:types '{s Shape} :defs defs :tenv tenv}
                                   [:call '= [:app 'writ.spec-demo.shapes/area 's] [:lit 9]]
                                   {'s [:Square 3]})))))
  (let [defs (defs-of 'writ.spec-demo.sort "writ/spec_demo/sort.clj")]
    (require 'writ.spec-demo.sort)
    (is (= :outside (sym/agrees? {:types '{xs (List Nat)} :defs defs :tenv {}}
                                 [:app 'writ.spec-demo.sort/isort 'xs] {'xs [3 1]})))))

(deftest sets-agree
  (require 'writ.spec-demo.cells)
  (let [defs (defs-of 'writ.spec-demo.cells "writ/spec_demo/cells.clj")
        worlds [#{} #{[0 0]} #{[0 1] [1 1] [2 1]} #{[0 0] [1 0] [0 1] [1 1]} #{[5 5] [-3 2]}]]
    (check defs '{c (Tuple Int Int)} 'writ.spec-demo.cells/neighbours '[c]
           (for [c [[0 0] [-4 9]]] {'c c}))
    (testing "membership in a stepped world of unknown size"
      (doseq [w worlds, cell [[0 0] [1 1] [1 0] [4 4]]]
        (let [opts {:types '{w (Set (Tuple Int Int)) cell (Tuple Int Int)} :defs defs :tenv {}}
              g [:call 'contains? [:app 'writ.spec-demo.cells/step 'w] 'cell]]
          ;; w is a predicate the solver may choose; pinning a finite set
          ;; to it is outside, so only the cell is pinned, and the check
          ;; is that the formula is not refuted at the real value
          (is (not= false (sym/agrees? opts g {'cell cell}))))))))

(deftest a-symmetric-rule-is-proved-for-every-world
  (let [r (spec/check 'writ.spec-demo.cells-spec {:seed 42})
        law (fn [nm] (first (filter #(= nm (:law %)) (:laws r))))]
    (is (:ok r) (:message r))
    (doseq [nm '[neighbours-are-the-eight-cells-around a-cell-lives-by-the-rule
                 the-plane-has-no-favoured-place]]
      (is (= :proved (:status (law nm))) (str nm)))
    (testing "a favoured place is refuted, and never proved"
      (let [r (spec/check 'writ.spec-demo.cells-spec {:seed 42 :target 'writ.spec-demo.cells-origin})]
        (is (not (:ok r)))
        (is (not= :proved (:status (first (filter #(= 'the-plane-has-no-favoured-place (:law %)) (:laws r))))))
        (is (not= :proved (:status (first (filter #(= 'a-cell-lives-by-the-rule (:law %)) (:laws r))))))
        (is (not-any? :prover-bug (:laws r)))))))

(deftest throws-agree
  (let [defs (defs-of 'writ.spec-demo.shapes "writ/spec_demo/shapes.clj")
        opts {:types '{xs (Tuple Int Keyword Int) i Int} :defs defs :tenv tenv}]
    (doseq [i [-1 0 2 3 9]]
      (is (true? (sym/throws-agree? opts [:call 'nth 'xs 'i] {'xs [4 :k -2] 'i i})) (str i)))
    (doseq [n [-3 0 12]]
      (is (true? (sym/throws-agree? {:types '{n Int} :defs defs :tenv tenv}
                                    [:app 'writ.spec-demo.shapes/bucket 'n] {'n n}))))))

(deftest values-of-any-shape-are-taken-apart
  (let [t0 (System/currentTimeMillis)
        r (spec/check 'writ.spec-demo.walk-spec {:seed 3 :cache false})
        status (into {} (map (juxt :law :status)) (:laws r))]
    (testing "seq, empty?, first and rest of a value of unknown shape agree"
      (is (= :proved (get status 'a-pair-binds-its-second)) (:message r))
      (is (= :proved (get status 'the-first-matching-clause-wins)) (:message r)))
    (testing "a recursion into a form of any depth gives up, and soon"
      (is (= :tested (get status 'a-depth-is-never-negative)) (:message r))
      (is (< (- (System/currentTimeMillis) t0) 120000)))))

(deftest some-over-a-seq-of-known-length-is-its-first-truthy-value
  (let [opts {:types '{a Int b Int} :defs {} :tenv {}}
        xs [:sq [:econs 'a [:econs 'b [:enil]]]]
        pos [:fn '[x] [:if [:call 'pos? 'x] 'x [:nil]]]]
    (is (sym/prove opts [] [:call '= [:call 'some pos xs] [:if [:call 'pos? 'a] 'a [:if [:call 'pos? 'b] 'b [:nil]]]]))
    (is (sym/prove opts [] [:call 'nil? [:call 'some pos [:sq [:enil]]]]))))

(deftest a-vector-of-unknown-length-is-a-vector
  (let [opts {:types '{as (Vec Int) k Keyword} :defs {} :tenv {}}
        proves? (fn [t] (try (boolean (sym/prove opts [] t)) (catch Throwable _ false)))]
    (is (proves? [:call 'vector? 'as]))
    (is (proves? [:call 'sequential? 'as]))
    (is (proves? [:call 'not [:call 'map? 'as]]))
    (is (proves? [:call 'not [:call 'nil? 'as]]))
    (is (proves? [:call '= [:call 'nth [:sq [:econs 'k [:econs 'as [:enil]]]] [:lit 1]] 'as]))
    (testing "what it holds stays unknown"
      (is (not (proves? [:call 'empty? 'as])))
      (is (not (proves? [:call 'not [:call 'empty? 'as]])))
      (is (not (proves? [:call '= 'as [:sq [:enil]]]))))))

(deftest the-rest-of-a-value-of-unknown-shape-is-never-a-vector
  (let [opts {:types '{x Any} :defs {} :tenv {}}]
    (is (sym/prove opts [] [:call 'not [:call 'vector? [:call 'rest 'x]]]))))

(deftest a-filtered-seq-compares-as-a-seq
  (let [opts {:types '{a Int b Int} :defs {} :tenv {}}
        le5 [:fn '[x] [:call '<= 'x [:lit 5]]]
        one [:sq [:econs 'a [:enil]]]
        none [:sq [:enil]]
        proves? (fn [hyps g] (boolean (try (sym/prove opts hyps g) (catch Throwable _ false))))]
    (is (proves? [] [:call '= [:call 'filter le5 one] [:if [:call '<= 'a [:lit 5]] one none]]))
    (testing "and nothing false about it is proved"
      (is (not (proves? [[:call '<= 'a [:lit 5]]] [:call 'not [:call '= [:call 'filter le5 one] one]])))
      (is (not (proves? [[:call '> 'a [:lit 5]]] [:call 'not [:call '= [:call 'filter le5 one] none]]))))))

(deftest sort-by-is-a-stable-sort-on-integer-keys
  (let [opts {:types '{a Int b Int} :defs {} :tenv {}}
        id [:fn '[x] 'x]
        zero [:fn '[x] [:lit 0]]
        ab [:sq [:econs 'a [:econs 'b [:enil]]]]
        ba [:sq [:econs 'b [:econs 'a [:enil]]]]
        le5 [:fn '[x] [:call '<= 'x [:lit 5]]]]
    (is (sym/prove opts [] [:call '= [:call 'sort-by id ab] [:if [:call '<= 'a 'b] ab ba]]))
    (is (sym/prove opts [] [:call '= [:call 'sort-by zero ab] ab]) "equal keys keep their order")
    (is (sym/prove opts [] [:call '= [:call 'count [:call 'sort-by id [:call 'filter le5 ab]]]
                            [:call 'count [:call 'filter le5 ab]]]))
    (is (not (try (sym/prove opts [] [:call '= [:call 'sort-by id ab] ab]) (catch Throwable _ false))))))

(deftest a-throw-folded-on-literals-is-a-throw-not-a-crash
  (let [r (spec/check 'writ.spec-demo.pick-spec {:seed 42 :adequacy false :cache false})
        l (first (filter #(= 'true-picks-one (:law %)) (:laws r)))]
    (is (not (str/includes? (str (:unproved l)) "the prover failed")) (str (:unproved l)))
    (is (= :proved (:status l)) (str (:unproved l)))))

(deftest a-core-fn-folded-on-literals-sees-the-value-it-is-given
  (let [v12 [:call 'vector [:lit 1] [:lit 2]]
        proves? (fn [t] (try (boolean (sym/prove {} [] t)) (catch Throwable _ false)))]
    (is (not (proves? [:call '= [:call 'str v12] [:lit "(1 2)"]])) "(str [1 2]) is \"[1 2]\"")
    (is (proves? [:call '= [:call 'str v12] [:lit "[1 2]"]]))
    (is (proves? [:call '= [:call 'str [:call 'list [:lit 1] [:lit 2]]] [:lit "(1 2)"]]))))

(deftest a-throw-in-a-folded-call-is-a-throw-of-the-call
  (is (sym/prove {} [] [:call '= [:call 'str [:call 'nth [:call 'vector [:lit 1]] [:lit 5]]] [:lit "x"]])))

(deftest nth-of-nil-is-nil
  (is (sym/prove {} [] [:call 'nil? [:call 'nth [:nil] [:lit 3]]]))
  (is (sym/prove {} [] [:call '= [:lit :d] [:call 'nth [:nil] [:lit 0] [:lit :d]]])))
