(ns writ.frame-test
  "Frames: an edge on a record state says which keys its step may
  change, and every other key must come through as it was."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.string :as str]
            [writ.spec :as spec]))

(defn- has? [r s] (str/includes? (:message r) s))

(defn- law-result [report nm]
  (first (filter #(= nm (:law %)) (:laws report))))

(defn- expansion-error [form]
  (try (macroexpand-1 form) nil
       (catch Throwable e (ex-message e))))

(deftest a-step-that-keeps-its-frame-passes-and-is-proved
  (let [r (spec/check 'writ.spec-demo.member-frame-spec {:seed 42})]
    (is (:ok r) (:message r))
    (is (= :proved (:status (law-result r 'membership:fresh:award:frame))))
    (is (= :proved (:status (law-result r 'membership:active:award:frame))))))

(deftest a-step-that-changes-another-key-fails
  (let [r (spec/check 'writ.spec-demo.member-frame-spec {:seed 42 :target 'writ.spec-demo.member-rename})]
    (is (not (:ok r)))
    (is (= :failed (:status (law-result r 'membership:fresh:award:frame))))
    (is (has? r "a award from fresh may change only :points"))))

(deftest a-frame-is-an-obligation
  (let [ids (set (map :id (spec/obligations 'writ.spec-demo.member-frame-spec)))]
    (is (contains? ids "frame.membership.fresh.award"))))

(deftest changes-names-keywords
  (is (str/includes? (expansion-error '(writ.spec/graph g {:states {:a A} :edges {:a {[f] {:to #{:a} :changes :x}}}}))
                     ":changes is a vector of the keys the step may change")))

(deftest changes-needs-a-record-state-with-those-keys
  (let [r (spec/check 'writ.spec-demo.frame-tuple-spec {:seed 42})]
    (is (not (:ok r)))
    (is (has? r ":changes needs a record state, but :hot is a (Tuple Keyword Int)")))
  (let [r (spec/check 'writ.spec-demo.frame-unknown-spec {:seed 42})]
    (is (not (:ok r)))
    (is (has? r ":changes names :pointz, which the record of :fresh does not have"))))
