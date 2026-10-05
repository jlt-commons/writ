(ns writ.draws-test
  "What a law is run on: values that reach the cases the code tells apart."
  (:require [clojure.test :refer [deftest is]]
            [clojure.string :as str]
            [writ.spec :as spec]))

(defn- law-result [r nm] (first (filter #(= nm (:law %)) (:laws r))))

(deftest a-keyword-field-is-drawn-from-what-the-code-tests-it-against
  ;; a Job's :status is any Keyword: drawn from every keyword, the
  ;; hypotheses on a due :ready job would never hold
  (let [r (spec/check 'writ.spec-demo.jobs-spec {:seed 7 :adequacy false})]
    (is (:ok r) (:message r))
    (is (not (str/includes? (:message r) "never held")) (:message r))))

(deftest an-implication-inside-a-law-is-a-value
  (let [r (spec/check 'writ.spec-demo.jobs-spec {:seed 7 :adequacy false})]
    (is (= :tested (:status (law-result r 'no-due-job-is-better))) (:message r))))

(deftest a-wrong-tie-break-is-caught
  ;; two due jobs of one priority, the earlier ready one with the higher
  ;; id: a law meets them only when both jobs are drawn :ready
  (let [r (spec/check 'writ.spec-demo.jobs-spec {:seed 7 :adequacy false :target 'writ.spec-demo.jobs-by-id})]
    (is (not (:ok r)))
    (is (= :failed (:status (law-result r 'no-due-job-is-better))) (:message r))))
