(ns writ.prove-test
  "The prover: its rules agree with the runtime, its model keeps the
  distinctions Clojure makes, and it proves laws from the code."
  (:require [clojure.test :refer [deftest is testing]]
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
