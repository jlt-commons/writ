(ns writ.prove-test
  "The prover: its rules agree with the runtime, its model keeps the
  distinctions Clojure makes, and it proves laws from the code."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.java.io]
            [writ.book]
            [writ.spec :as spec]
            [writ.prove :as prover]
            [writ.prove.term :as t]
            [writ.prove.rewrite :as rw]))

(defn- norm
  ([x] (norm {} x))
  ([opts x] (rw/normalize (rw/context opts) x)))

;; --- phase 0: the rules agree with the runtime ------------------------------

(deftest every-pattern-rule-agrees-with-the-runtime
  (let [r (rw/self-test)]
    (is (:ok r) (pr-str (:failures r)))
    (is (<= 35 (:checked r)))))

(deftest a-wrong-rule-is-caught-by-the-self-test
  ;; (rest nil) is (), not nil
  (let [r (rw/self-test '[[rest-nil-wrong [:call rest [:nil]] [:nil]]] 100 42)]
    (is (not (:ok r)))
    (is (= 'rest-nil-wrong (:rule (first (:failures r)))))))

(deftest the-normaliser-agrees-with-the-runtime-on-closed-terms
  (let [r (rw/ground-check 400 42)]
    (is (:ok r) (pr-str (:counterexample r)))))

;; --- the model keeps Clojure's distinctions ---------------------------------

(deftest nil-and-empty-are-different-values
  (is (= [:lit false] (norm [:call '= [:nil] [:sq [:enil]]])))
  (is (= [:sq [:enil]] (norm [:call 'rest [:nil]])) "rest is never nil")
  (is (= [:nil] (norm [:call 'next (t/seq-term [[:lit 1]])])) "next of one element is nil")
  (is (= [:nil] (norm [:call 'seq [:sq [:enil]]]))))

(deftest equality-follows-clojure
  (testing "sequentials compare element by element, whatever their kind"
    (is (= [:lit true] (norm [:call '= (t/value->term [1 2]) (t/value->term '(1 2))]))))
  (testing "an integer never equals a float"
    (is (= [:lit false] (norm [:call '= [:lit 1] [:lit 1.0]]))))
  (testing "a term is = to itself only when no float can be inside"
    (is (= [:lit true] (norm {:types {'xs '(List Nat)}} [:call '= 'xs 'xs])))
    (is (= [:call '= 'xs 'xs] (norm {:types {'xs '(List Double)}} [:call '= 'xs 'xs])))))

(deftest integers-are-exact-and-floats-get-no-algebra
  (let [ctx {:types {'a 'Nat 'b 'Nat}}]
    (is (= (norm ctx [:call '+ 'a 'b]) (norm ctx [:call '+ 'b 'a])) "+ commutes on integers")
    (is (= [:lit true] (norm ctx [:call '<= [:lit 0] 'a])) "a Nat is not negative")
    (is (= [:lit false] (norm ctx [:call '< 'a 'a]))))
  (testing "untyped operands stay as they are"
    (is (= [:call '+ 'x 'y] (norm [:call '+ 'x 'y])))))

;; --- phase 1: laws proved from the code ---------------------------------------

(defn- law-result [report nm]
  (first (filter #(= nm (:law %)) (:laws report))))

(deftest insert-adds-is-proved-by-induction
  (let [r (spec/check 'writ.spec-demo.sort-spec {:seed 42})
        l (law-result r 'insert-adds)]
    (is (:ok r) (:message r))
    (is (= :proved (:status l)) (pr-str l))
    (is (re-find #"by induction on xs, splitting on" (str (:proof l))))
    (testing "a proved law was still run"
      (is (= 100 (:trials l))))))

(deftest a-tree-law-is-proved-by-induction-on-the-datatype
  (let [r (spec/check 'writ.spec-demo.tree-spec {:seed 42})
        l (law-result r 'size-counts)]
    (is (:ok r) (:message r))
    (is (= :proved (:status l)) (pr-str l))
    (is (re-find #"by induction on t" (str (:proof l))))))

(deftest laws-outside-the-model-stay-tested-with-a-reason
  (let [r (spec/check 'writ.spec-demo.sort-spec {:seed 42})]
    (is (= :tested (:status (law-result r 'smallest-first))))
    (is (string? (:unproved (law-result r 'smallest-first))))))

(deftest a-false-law-is-never-proved
  (testing "insert-adds is false when insert drops duplicates"
    (let [r (spec/check 'writ.spec-demo.sort-spec {:seed 42 :target 'writ.spec-demo.sort-dedup})]
      (is (= :failed (:status (law-result r 'insert-adds))))
      (is (not-any? :prover-bug (:laws r)))))
  (testing "on every broken sort, no law is both proved and refuted"
    (doseq [target '[writ.spec-demo.sort-desc writ.spec-demo.sort-conj writ.spec-demo.sort-identity]]
      (let [r (spec/check 'writ.spec-demo.sort-spec {:seed 42 :target target})]
        (is (not-any? :prover-bug (:laws r)) (str target)))))
  (testing "insert-adds still holds when the order is flipped, and is proved"
    (let [r (spec/check 'writ.spec-demo.sort-spec {:seed 42 :target 'writ.spec-demo.sort-desc})]
      (is (= :proved (:status (law-result r 'insert-adds)))))))

(deftest proving-can-be-turned-off
  (let [r (spec/check 'writ.spec-demo.sort-spec {:seed 42 :prove false})]
    (is (= :tested (:status (law-result r 'insert-adds))))))

(deftest the-prover-reads-the-code-it-proves
  (require 'writ.spec-demo.sort)
  (let [[defs] (prover/definitions [['writ.spec-demo.sort
                                     (writ.book/read-forms (clojure.java.io/resource "writ/spec_demo/sort.clj"))]])
        f (get defs 'writ.spec-demo.sort/insert)]
    (testing "a translated definition computes what the fn computes"
      (doseq [[x xs] [[3 '(1 2 5)] [0 []] [9 [1 9 12]] [4 nil]]]
        (is (= ((resolve 'writ.spec-demo.sort/insert) x xs)
               (t/evaluate (:body f) {'x x 'xs xs})))))
    (is (:recursive? f))))

(deftest a-fact-can-settle-a-comparison-false
  ;; from 0 <= x - h - 1 (h < x), 0 <= h - x (x <= h) must come out false
  (let [ctx (rw/assume (rw/context {:types '{x Nat h Nat}})
                       [:le [:lin -1 '[[h -1] [x 1]]]] true)]
    (is (false? (rw/decide ctx [:le [:lin 0 '[[h 1] [x -1]]]])))))

;; --- soundness ----------------------------------------------------------------

(deftest an-assumed-test-is-a-value-only-when-it-is-a-boolean
  (testing "(seq xs) assumed truthy is not true"
    (is (not= [:lit true]
              (norm {:types '{xs (List Int)}}
                    [:if [:call 'seq 'xs] [:call '= [:call 'seq 'xs] [:lit true]] [:lit true]]))))
  (testing "(first xs) assumed falsy may be nil, not false"
    (is (not= [:lit true]
              (norm {:types '{xs (List Bool)}}
                    [:if [:call 'first 'xs] [:lit true] [:call '= [:call 'first 'xs] [:lit false]]]))))
  (testing "a boolean test is still its assumed value"
    (is (= [:lit true]
           (norm {:types '{xs (List Int)}}
                 [:if [:call 'empty? 'xs] [:call '= [:call 'empty? 'xs] [:lit true]] [:lit true]])))))

(deftest substitution-does-not-capture
  (let [f (t/subst [:fn '[a] [:call '+ 'a 'b]] {'b 'a})]
    (is (= 11 (t/evaluate [:ap f [:lit 10]] {'a 1})))))

(deftest substitution-leaves-quoted-symbols-alone
  (is (= [:lit 'x] (t/subst [:lit 'x] {'x [:lit 1]})))
  (is (= [:call '= [:lit 'x] [:lit 1]] (t/subst [:call '= [:lit 'x] 'x] {'x [:lit 1]}))))

(deftest a-recursive-datatype-is-float-free
  (let [ctx (rw/context {:tenv '{Tree {:ctors {Leaf {:fields []} Node {:fields [Tree Nat Tree]}}}}
                         :types '{t Tree}})
        r (deref (future (rw/float-free? ctx 't)) 5000 ::timeout)]
    (is (true? r))))

(deftest nth-of-nil-is-nil
  (is (= [:nil] (norm [:call 'nth [:nil] [:lit 0]])))
  (is (= [:nil] (norm [:call 'nth [:nil] [:lit -1]])))
  (is (= [:lit :d] (norm [:call 'nth [:nil] [:lit 3] [:lit :d]]))))

;; --- phase 2: core fns as values ------------------------------------------------

(deftest a-core-fn-can-be-a-value
  (let [ctx (writ.prove.translate/context {})
        tm #(writ.prove.translate/lower-term ctx '[xs] %)]
    (is (= [:call 'apply [:cfn '<=] 'xs] (tm '(apply <= xs))))
    (is (= [:call 'filter [:cfn 'odd?] 'xs] (tm '(filter odd? xs))))))

(deftest apply-of-a-comparison-walks-the-list
  (is (= [:lit true] (norm [:call 'apply [:cfn '<=] (t/value->term [1 2 2 5])])))
  (is (= [:lit false] (norm [:call 'apply [:cfn '<] (t/value->term [1 2 2 5])])))
  (is (= [:lit 10] (norm [:call 'apply [:cfn '+] (t/value->term [1 2 3 4])])))
  (testing "on two unknowns it is the comparison"
    (is (= (norm {:types '{a Nat b Nat}} [:call '<= 'a 'b])
           (norm {:types '{a Nat b Nat}} [:call 'apply [:cfn '<=] [:sq [:econs 'a [:econs 'b [:enil]]]]]))))
  (testing "applying a core fn value calls it"
    (is (= [:lit 4] (norm [:ap [:cfn 'inc] [:lit 3]])))))

(deftest apply-rules-agree-with-the-runtime
  (let [r (rw/self-test (filter #(re-find #"^apply" (name (first %))) rw/pattern-rules) 200 42)]
    (is (:ok r) (pr-str (:failures r)))
    (is (<= 10 (:checked r)))))

(deftest comparisons-follow-from-chains-of-facts
  ;; a <= b, b <= c, c <= d  gives  a <= d, and settles d < a false
  (let [le (fn [x y] [:le [:lin 0 [[y 1] [x -1]]]])
        ctx (reduce (fn [c f] (rw/assume c f true))
                    (rw/context {:types '{a Int b Int c Int d Int}})
                    [(le 'a 'b) (le 'b 'c) (le 'c 'd)])]
    (is (true? (rw/decide ctx (le 'a 'd))))
    (is (false? (rw/decide ctx [:le [:lin -1 '[[a 1] [d -1]]]])))
    (is (nil? (rw/decide ctx (le 'd 'a))) "d <= a is open")
    (testing "integers: 2x >= 1 means x >= 1"
      (let [ctx (rw/assume (rw/context {:types '{x Int}}) [:le [:lin -1 '[[x 2]]]] true)]
        (is (true? (rw/decide ctx [:le [:lin -1 '[[x 1]]]])))))))

;; --- phase 2: case analysis and lemmas --------------------------------------------

(deftest insert-keeps-sorted-is-proved-by-looking-at-the-tail
  (let [l (law-result (spec/check 'writ.spec-demo.sort-spec {:seed 42}) 'insert-keeps-sorted)]
    (is (= :proved (:status l)) (pr-str l))
    (is (re-find #"by induction on xs" (:proof l)))
    (is (re-find #"cases on xs-t" (:proof l)))))

(deftest sorted-cites-insert-keeps-sorted
  (let [l (law-result (spec/check 'writ.spec-demo.sort-spec {:seed 42}) 'sorted)]
    (is (= :proved (:status l)) (pr-str l))
    (is (= '[insert-keeps-sorted] (:lemmas l)))
    (is (re-find #"citing insert-keeps-sorted" (:proof l)))))

(deftest a-law-only-tested-is-never-a-lemma
  (testing "with insert-keeps-sorted refuted, sorted cannot cite it"
    (let [r (spec/check 'writ.spec-demo.sort-spec {:seed 42 :target 'writ.spec-demo.sort-desc})]
      (is (not= :proved (:status (law-result r 'insert-keeps-sorted))))
      (is (not= :proved (:status (law-result r 'sorted))))
      (is (not-any? :prover-bug (:laws r))))))
