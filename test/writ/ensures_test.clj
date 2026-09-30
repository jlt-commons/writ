(ns writ.ensures-test
  "Dependent signatures: an ann's :ensures says what a result must meet
  given the arguments, and :requires what the arguments must meet.  Each
  :ensures is a law, proved and cited like one; both are checked on every
  call while the laws run."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.string :as str]
            [writ.spec :as spec]))

(defn- has? [r s] (str/includes? (:message r) s))

(defn- law-result [report nm]
  (first (filter #(= nm (:law %)) (:laws report))))

(defn- expansion-error [form]
  (try (macroexpand-1 form) nil
       (catch Throwable e (ex-message e))))

(deftest an-ensures-is-a-law-of-the-spec
  (let [r (spec/check 'writ.spec-demo.clip-spec {:seed 42})]
    (is (:ok r) (:message r))
    (is (#{:proved :tested} (:status (law-result r 'take-upto:ensures))))
    (is (= :proved (:status (law-result r 'clamp:ensures))) (:unproved (law-result r 'clamp:ensures)))))

(deftest a-result-that-breaks-its-ensures-fails
  (let [r (spec/check 'writ.spec-demo.clip-spec {:seed 42 :target 'writ.spec-demo.clip-over})]
    (is (not (:ok r)))
    (is (= :failed (:status (law-result r 'take-upto:ensures))))
    (is (has? r "`take-upto` returns"))
    (is (has? r "which breaks its :ensures"))))

(deftest a-call-that-breaks-requires-fails-at-the-call
  (let [r (spec/check 'writ.spec-demo.clip-spec {:seed 42 :target 'writ.spec-demo.clip-backwards})]
    (is (not (:ok r)))
    (is (has? r "`clamp` requires (<= lo hi), but is called with [9 0"))))

(deftest ensures-and-requires-take-the-fns-arguments
  (is (str/includes? (expansion-error '(writ.spec/ann f [Nat Nat -> Nat] {:ensures (fn [a r] true)}))
                     ":ensures takes the fn's 2 argument(s) and its result"))
  (is (str/includes? (expansion-error '(writ.spec/ann f [Nat -> Nat] {:requires (fn [a b] true)}))
                     ":requires takes the fn's 1 argument(s)"))
  (is (str/includes? (expansion-error '(writ.spec/ann f [Nat -> Nat] {:returns 1}))
                     "unknown options")))

(deftest ensures-are-obligations-and-in-the-plan
  (let [ids (set (map :id (spec/obligations 'writ.spec-demo.clip-spec)))]
    (is (contains? ids "ensures.clamp")))
  (let [p (spec/plan 'writ.spec-demo.clip-spec)]
    (is (str/includes? p "requires: (<= lo hi)"))
    (is (str/includes? p "ensures: (<= lo r hi)"))))

(deftest a-contract-s-names-are-its-own
  (let [r (spec/check 'writ.spec-demo.tag-spec {:seed 42})]
    (is (:ok r) (:message r))
    (is (#{:proved :tested} (:status (first (filter #(= 'label:ensures (:law %)) (:laws r))))))
    (is (#{:proved :tested} (:status (first (filter #(= 'add-item:ensures (:law %)) (:laws r))))))))
