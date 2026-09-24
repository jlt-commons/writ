(ns writ.symbolic-test
  "Symbolic evaluation agrees with running the code: for concrete inputs,
  the formula for (= (f x) out) holds exactly when f returns out."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.java.io]
            [writ.book]
            [writ.prove :as prover]
            [writ.prove.symbolic :as sym]
            [writ.spec :as spec]))

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
