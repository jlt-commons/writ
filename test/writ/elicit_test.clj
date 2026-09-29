(ns writ.elicit-test
  "What to ask a spec's owner: the decisions a spec's types raise, which
  code will make one way or another whether anyone chose it."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.string :as str]
            [writ.spec :as spec]))

(defn- of-class [asks k] (first (filter #(= k (:class %)) asks)))

(deftest collections-ask-about-empty-and-integers-about-sign
  (let [asks (spec/elicit 'writ.spec-demo.clip-spec)]
    (is (= '[take-upto] (:fns (of-class asks :empty))))
    (is (= '[clamp clamp-digit take-upto] (:fns (of-class asks :zero-and-negative))))
    (is (string? (:ask (of-class asks :empty))))))

(deftest optional-values-ask-what-absent-means
  (let [asks (spec/elicit 'writ.spec-demo.member-spec)]
    (is (= '[award nickname] (:fns (of-class asks :absent))))))

(deftest each-graph-asks-about-the-whole-life
  (let [asks (spec/elicit 'writ.spec-demo.member-spec)]
    (is (= '[membership] (:graphs (of-class asks :whole-life))))))

(deftest nothing-to-ask-is-nothing
  (let [asks (spec/elicit 'writ.spec-demo.member-spec)]
    (is (nil? (of-class asks :precision)))))

(deftest the-plan-asks-them
  (let [p (spec/plan 'writ.spec-demo.clip-spec)]
    (is (str/includes? p "ask the spec's owner"))
    (is (str/includes? p "take-upto"))))
