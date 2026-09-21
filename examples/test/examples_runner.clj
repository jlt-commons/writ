(ns examples-runner
  "Hand-rolled test runner so this project depends on nothing but writ.
  `jolt -M:test` requires the test namespaces and exits non-zero on failure."
  (:require [clojure.test :as t]
            examples-test))

(def test-namespaces '[examples-test])

(defn -main [& _]
  (let [{:keys [fail error]} (apply t/run-tests test-namespaces)]
    (System/exit (if (zero? (+ (or fail 0) (or error 0))) 0 1))))
