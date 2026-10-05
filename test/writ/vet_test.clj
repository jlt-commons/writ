(ns writ.vet-test
  "A spec checked before its code is written."
  (:require [clojure.test :refer [deftest is]]
            [clojure.string :as str]
            [writ.spec :as spec]))

(defn- has? [r s] (str/includes? (:message r) s))

(deftest a-spec-whose-code-is-not-written-is-checked-alone
  (let [r (spec/check 'writ.spec-demo.unwritten-spec)]
    (is (not (:ok r)) "no code, no pass")
    (is (:no-code r))
    (is (:spec-ok r) (:message r))
    (is (has? r "no implementation yet"))
    (is (nil? (find-ns 'writ.spec-demo.unwritten)) "the stand-ins are gone after")))

(deftest a-spec-that-contradicts-itself-is-caught-before-the-code
  (let [r (spec/check 'writ.spec-demo.unwritten-wrong-spec)]
    (is (not (:spec-ok r)))
    (is (has? r "law `the-price` contradicts the example (price 2) => 7") (:message r))
    (is (has? r "example (price 0) breaks `price`'s :requires") (:message r))
    (is (has? r "law `arithmetic` is vacuous") (:message r))))

(deftest an-example-of-an-unsigned-fn-is-named
  (let [r (spec/check 'writ.spec-demo.unwritten-unsigned-spec)]
    (is (:no-code r) (:message r))
    (is (has? r "example (bump 1): the spec gives `bump` no signature") (:message r))))
