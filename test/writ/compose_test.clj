(ns writ.compose-test
  "A spec built on another: the component taken at its spec."
  (:require [clojure.test :refer [deftest is]]
            [clojure.string :as str]
            [writ.spec :as spec]))

(defn- has? [r s] (str/includes? (:message r) s))
(defn- law-result [r nm] (first (filter #(= nm (:law %)) (:laws r))))

(deftest a-workflow-is-proved-from-its-components-laws
  (let [r (spec/check 'writ.spec-demo.shop-spec {:seed 7})]
    (is (:ok r) (:message r))
    (is (= :proved (:status (law-result r 'a-wrong-password-pays-nothing))))
    (is (has? r "are taken at that spec"))))

(deftest a-workflow-that-breaks-a-components-requires-fails
  (let [r (spec/check 'writ.spec-demo.shop-spec {:seed 7 :target 'writ.spec-demo.shop-eager})]
    (is (not (:ok r)))
    (is (has? r "`writ.spec-demo.auth/charge` requires (authed? s)") (:message r))))

(deftest a-workflow-on-a-failing-component-fails
  (let [r (spec/check 'writ.spec-demo.shop-on-strict-spec {:seed 7})]
    (is (not (:ok r)))
    (is (has? r "builds on writ.spec-demo.auth-strict-spec, which fails its own check") (:message r))))

(deftest a-refinement-that-only-names-a-record-is-a-plain-state
  (let [r (spec/check 'writ.spec-demo.auth-spec {:seed 7})]
    (is (:ok r) (:message r))))

(deftest a-workflow-names-its-components-types
  (let [r (spec/check 'writ.spec-demo.shop-typed-spec {:seed 7})]
    (is (:ok r) (:message r))))

;; --- what the prover reads ---------------------------------------------------------

(deftest a-store-of-named-records-is-proved
  (let [r (spec/check 'writ.spec-demo.lockout-spec {:seed 7})]
    (is (:ok r) (:message r))))

(deftest a-pipeline-is-proved-by-position
  (let [r (spec/check 'writ.spec-demo.tags-spec {:seed 7})]
    (is (:ok r) (:message r))
    (is (re-find #"element by element" (str (:proof (law-result r 'tagging-keeps-the-weights)))))))
