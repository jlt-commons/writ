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
    (is (re-find #"by induction on xs" (str (:proof l))))
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

(deftest a-fn-name-is-not-a-variable
  (is (= '#{x} (t/vars [:call 'count [:app 'my/f 'x]])))
  (is (= [:call 'count [:lit 1]] (t/subst [:call 'count 'count] '{count [:lit 1]}))))

(deftest a-call-on-an-if-is-an-if-of-calls
  (let [ctx {:types '{a Nat b Nat}}
        c [:call '<= 'a 'b]
        n (norm ctx [:call 'count [:if c (t/value->term [1 2]) (t/value->term [1])]])]
    (is (= :if (first n)))
    (is (= [:lit 2] (nth n 2)))
    (is (= [:lit 1] (nth n 3)))))

(deftest permutation-is-proved-by-generalising-the-recursive-call
  (let [l (law-result (spec/check 'writ.spec-demo.sort-spec {:seed 42}) 'permutation)]
    (is (= :proved (:status l)) (pr-str l))
    (is (re-find #"generalising \(isort xs-t\)" (:proof l)))))

;; --- loops ----------------------------------------------------------------------

(defn- run-def
  "Run translated definition q on args, its calls to other translated
  definitions run the same way."
  [defs q args]
  (let [{:keys [params body]} (get defs q)]
    (t/evaluate body (zipmap params args)
                (fn [n] (if (contains? defs n)
                          (delay (fn [& as] (run-def defs n as)))
                          (resolve n))))))

(deftest a-loop-is-a-local-recursive-definition
  (require 'writ.spec-demo.total)
  (let [[defs] (prover/definitions [['writ.spec-demo.total
                                     (writ.book/read-forms (clojure.java.io/resource "writ/spec_demo/total.clj"))]])
        f (get defs 'writ.spec-demo.total/total)]
    (is (nil? (:outside f)) (pr-str f))
    (testing "the translation computes what the fn computes"
      (doseq [xs ['() [3] '(1 2 3) nil]]
        (is (= ((resolve 'writ.spec-demo.total/total) xs)
               (run-def defs 'writ.spec-demo.total/total [xs]))))))
  (let [l (law-result (spec/check 'writ.spec-demo.total-spec {:seed 42 :adequacy false}) 'total-of-two)]
    (is (= :proved (:status l)) (pr-str l))))

(deftest reduce-folds-a-list
  (let [plus [:fn '[a b] [:call '+ 'a 'b]]]
    (is (= [:lit 6] (norm [:call 'reduce plus [:lit 0] (t/value->term [1 2 3])])))
    (is (= [:lit 0] (norm [:call 'reduce plus [:lit 0] [:nil]])))
    (testing "over concatenated colls it folds one after the other"
      (is (= (norm {:types '{xs {:elems Nat} ys {:elems Nat}}}
                   [:call 'reduce plus [:call 'reduce plus [:lit 0] [:sq 'xs]] [:sq 'ys]])
             (norm {:types '{xs {:elems Nat} ys {:elems Nat}}}
                   [:call 'reduce plus [:lit 0] [:sq [:eapp 'xs 'ys]]]))))
    (testing "a fn that may return reduced is not unrolled"
      (is (= :call (first (norm [:call 'reduce [:fn '[a b] [:ap 'g 'a 'b]] [:lit 0]
                                 (t/value->term [1 2])])))))))

;; --- phase 3: folds and accumulators --------------------------------------------

(deftest a-fold-into-an-accumulator-is-proved-by-generalising-it
  (let [r (spec/check 'writ.spec-demo.total-spec {:seed 42})]
    (is (:ok r) (:message r))
    (doseq [nm '[total-sums size-counts reduce-sums]]
      (let [l (law-result r nm)]
        (is (= :proved (:status l)) (pr-str l))
        (is (re-find #"generalising the accumulator of" (:proof l)) (pr-str l))
        (is (not-any? '#{accumulator-adds accumulator-is-an-integer} (:lemmas l)))))
    (testing "a reduce over concatenated colls, citing the law before it"
      (is (= :proved (:status (law-result r 'reduce-appends))))
      (is (= '[reduce-sums] (:lemmas (law-result r 'reduce-appends)))))))

(deftest a-broken-fold-is-never-proved
  (let [r (spec/check 'writ.spec-demo.total-spec {:seed 42 :target 'writ.spec-demo.total-bad})]
    (doseq [nm '[total-sums size-counts reduce-sums]]
      (is (= :failed (:status (law-result r nm))) (str nm)))
    (is (not-any? :prover-bug (:laws r)))))

;; --- the proof checker --------------------------------------------------------------

(defn- law-input [spec-ns nm]
  (require spec-ns)
  (let [e (get @spec/registry spec-ns)
        target (:target e)
        _ (require target)
        l (first (filter #(= nm (:name %)) (:laws e)))
        qp (#'spec/qualify (#'spec/desugar (:prop l)) #{} (set (keys (ns-publics (the-ns target))))
                           (set (keys (ns-interns (the-ns spec-ns)))) target spec-ns)
        [defs own] (prover/definitions [[target (writ.book/read-forms (#'spec/source-url target))]
                                        [spec-ns (writ.book/read-forms (#'spec/source-url spec-ns))]])
        [bs body] (writ.prove.scheme/split-foralls qp)
        rets (into {} (for [[f sig] (:anns e)] [(symbol (str target) (str f)) (:ret sig)]))]
    {:law {:prop qp :defs defs :own own :target target :tenv (#'spec/tenv-of (:data e)) :rets rets}
     :opts {:defs defs :tenv (#'spec/tenv-of (:data e))
            :types (into {} (map (fn [[x ty]] [x (writ.prove.scheme/plain ty)])) bs)
            :fuel 20000 :lemmas [] :rets rets}
     :goal (writ.prove.scheme/goal (writ.prove.translate/context own) (mapv first bs) body)}))

(deftest every-proof-is-replayed-by-the-checker
  (let [{:keys [law opts goal]} (law-input 'writ.spec-demo.sort-spec 'insert-keeps-sorted)
        r (prover/prove-law law)]
    (is (:proved r))
    (is (= {:ok true} (writ.prove.check/check-proof opts goal (:trace r))))
    (testing "a proof with a case left out is rejected"
      (let [bad (update-in (:trace r) [:cases] pop)]
        (is (re-find #"the cases of `xs` are" (:reason (writ.prove.check/check-proof opts goal bad))))))
    (testing "a goal claimed closed by rewriting that is not"
      (let [bad (assoc-in (:trace r) [:cases 2 :proof 0] {:by :rewriting})]
        (is (re-find #"does not rewrite to true" (:reason (writ.prove.check/check-proof opts goal bad))))))
    (testing "a split that proves only one side"
      (is (not (:ok (writ.prove.check/check-proof opts goal
                                                  (assoc-in (:trace r) [:cases 2 :proof 0 :else]
                                                            {:by :rewriting}))))))
    (testing "induction on a variable at the wrong type"
      (is (re-find #"induction on `xs`"
                   (:reason (writ.prove.check/check-proof opts goal (assoc (:trace r) :ty '(List Int))))))))
  (testing "a generalisation and an accumulator replay too"
    (doseq [[sp nm] '[[writ.spec-demo.sort-spec permutation] [writ.spec-demo.total-spec size-counts]]]
      (let [{:keys [law opts goal]} (law-input sp nm)
            r (prover/prove-law law)]
        (is (:proved r) (str nm))
        (is (= {:ok true} (writ.prove.check/check-proof opts goal (:trace r))) (str nm))))))

;; --- constants and more of clojure.core ------------------------------------------

(deftest named-constants-and-core-fns-are-proved
  (let [r (spec/check 'writ.spec-demo.court-spec {:seed 42})]
    (is (:ok r) (:message r))
    (doseq [l '[a-paddle-stays-on-the-court up-moves-two-rows-away-from-the-wall
                a-tick-moves-at-most-two-rows up-and-down-part-ways
                every-key-keeps-the-paddle-on some-key-moves-it-up
                safe-means-get-head-or-put distance-is-the-gap]]
      (is (= :proved (:status (law-result r l))) (str l ": " (pr-str (law-result r l)))))
    (testing "a law over two Ints rejects a constant distance: each variable gets its own samples"
      (is (= [] (:gaps r))))))

(deftest an-open-clamp-is-refuted-not-proved
  (let [r (spec/check 'writ.spec-demo.court-spec {:seed 42 :target 'writ.spec-demo.court-open})]
    (is (= :failed (:status (law-result r 'a-paddle-stays-on-the-court))))
    (is (not-any? :prover-bug (:laws r)))))

(deftest a-constant-is-its-value
  (require 'writ.spec-demo.court)
  (let [[defs] (prover/definitions [['writ.spec-demo.court
                                     (writ.book/read-forms (clojure.java.io/resource "writ/spec_demo/court.clj"))]])]
    (doseq [[y k] [[-5 [:Up]] [0 [:Down]] [40 [:Down]] [37 [:Idle]] [100 [:Up]]]]
      (is (= ((resolve 'writ.spec-demo.court/move) y k)
             (t/evaluate (:body (get defs 'writ.spec-demo.court/move)) {'y y 'key k}))))
    (is (= true (t/evaluate (:body (get defs 'writ.spec-demo.court/safe?)) {'method :head})))
    (is (= false (t/evaluate (:body (get defs 'writ.spec-demo.court/safe?)) {'method :post})))))

(deftest literal-arithmetic-is-computed
  (is (= [:lit 4] (norm [:call 'quot [:lit 9] [:lit 2]])))
  (is (= [:lit 2] (norm [:call 'mod [:lit -3] [:lit 5]])))
  (is (= [:lit -3] (norm [:call 'rem [:lit -3] [:lit 5]])))
  (testing "a division by zero is left alone, not folded"
    (is (= [:call 'quot [:lit 1] [:lit 0]] (norm [:call 'quot [:lit 1] [:lit 0]])))))
