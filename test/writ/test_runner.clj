(ns writ.test-runner
  "Hand-rolled test runner. Keeps the project dependency-free: `jolt -M:test`
  requires every listed test namespace and exits non-zero on any failure."
  (:require [clojure.test :as t]
            writ.check-test
            writ.book-test
            writ.gaps-test
            writ.spec-test
            writ.prove-test
            writ.evidence-test
            writ.solve-test))

(def test-namespaces
  '[writ.check-test writ.book-test writ.gaps-test writ.spec-test writ.prove-test writ.evidence-test writ.solve-test])

(defn -main [& _]
  (let [{:keys [fail error]} (apply t/run-tests test-namespaces)]
    (System/exit (if (zero? (+ (or fail 0) (or error 0))) 0 1))))
