(ns writ.speed-test
  "What a check costs, and the changes that make it cost less without
  changing what it finds."
  (:require [clojure.test :refer [deftest is testing]]
            [writ.spec :as spec]))

;; --- timings ----------------------------------------------------------------------

(deftest a-report-says-where-its-time-went
  (let [r (spec/check 'writ.spec-demo.gap-spec {:seed 1})
        t (:timings r)]
    (is (:ok r) (:message r))
    (is (= #{:static :tests :prover :more-trials :adequacy :graphs :total} (set (keys t))))
    (is (every? #(and (number? %) (>= % 0)) (vals t)))
    (is (>= (:total t) (reduce + (vals (dissoc t :total)))))))

(deftest each-tested-law-says-what-its-trials-cost
  (let [r (spec/check 'writ.spec-demo.gap-spec {:seed 1 :adequacy false})]
    (is (seq (:laws r)))
    (is (every? #(number? (:test-ms %)) (remove #(= :vacuous (:status %)) (:laws r))))))
