(ns examples-runner
  "`jolt -M:test` runs every example's checks and exits non-zero on a failure.
  `jolt -M:test pong.core-test` runs only the namespaces named."
  (:require [clojure.test :as t]
            fetch.core-test
            life.core-test
            pong.core-test
            screens.core-test
            shortener.core-test))

(def test-namespaces
  '[pong.core-test life.core-test screens.core-test shortener.core-test fetch.core-test])

;; a check can run for minutes, so say which test is running and how long
;; each took, rather than print nothing until the end
(defmethod t/report :begin-test-var [m]
  (println "  " (-> m :var meta :name) "...")
  (flush))

(defmethod t/report :end-test-var [m]
  (println "  " (-> m :var meta :name) "done")
  (flush))

(defn -main [& args]
  (let [nses (if (seq args) (map symbol args) test-namespaces)
        _ (when-let [bad (seq (remove (set test-namespaces) nses))]
            (println "not an example test namespace:" (vec bad))
            (System/exit 1))
        {:keys [fail error]} (apply t/run-tests nses)]
    (System/exit (if (zero? (+ (or fail 0) (or error 0))) 0 1))))
