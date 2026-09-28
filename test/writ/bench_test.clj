(ns writ.bench-test
  "The prover's benchmark: a row per law tried, and what a change did."
  (:require [clojure.test :refer [deftest is testing]]
            [writ.bench :as bench]))

(deftest a-bench-has-a-row-per-law-the-prover-tried
  (let [rows (bench/run '[writ.spec-demo.index-spec])
        {:keys [laws proved winners]} (bench/summary rows)]
    (is (= 4 laws))
    (is (= 4 proved))
    (is (= {:climb 4} winners))
    (is (every? #(pos? (:fuel %)) rows))
    (is (every? #(seq (:attempts %)) rows))))

(deftest compare-lists-what-a-change-gained-and-lost
  (let [row (fn [law proved? ms] {:spec 's :law law :proved? proved? :ms ms})
        c (bench/compare [(row 'a true 10) (row 'b false 10) (row 'c true 100) (row 'd true 1)]
                         [(row 'a false 10) (row 'b true 10) (row 'c true 1000) (row 'e true 1)])]
    (is (= '[[s b]] (:gained c)))
    (is (= '[[s a]] (:lost c)))
    (is (= '[[[s c] 100 1000]] (:slower c)))
    (is (= '[[s e]] (:new c)))
    (is (= '[[s d]] (:gone c)))))

(deftest the-default-config-is-todays-prover
  (let [rows (bench/run '[writ.spec-demo.index-spec])
        same (bench/run '[writ.spec-demo.index-spec] {:prover writ.prove/default-config})]
    (is (= (map (juxt :law :status :winner :fuel) rows) (map (juxt :law :status :winner :fuel) same)))))

(deftest a-tuning-run-compares-each-config-with-the-default
  (let [[r] (bench/tune [{:depth 2}] '[writ.spec-demo.index-spec] '[writ.spec-demo.walk-spec])]
    (is (= {:depth 2} (:config r)))
    (is (every? #(contains? (get r %) :compare) [:tune :held-out]))
    (is (re-find #"tune: \d+ gained, \d+ lost" (bench/tune-report [r])))))
