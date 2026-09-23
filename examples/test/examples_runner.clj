(ns examples-runner
  "`jolt -M:test` runs every example's checks and exits non-zero on a failure."
  (:require [clojure.test :as t]
            fetch.core-test
            life.core-test
            pong.core-test
            screens.core-test
            shortener.core-test))

(def test-namespaces
  '[pong.core-test life.core-test screens.core-test shortener.core-test fetch.core-test])

(defn -main [& _]
  (let [{:keys [fail error]} (apply t/run-tests test-namespaces)]
    (System/exit (if (zero? (+ (or fail 0) (or error 0))) 0 1))))
