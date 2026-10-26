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

(deftest reuse-metrics-count-actual-citations-and-spec-diagnostics
  (let [rows [{:spec 'a :suggestion {:hint '(hint l {:use [used used-other]})}
               :reuse {:spec 'a :candidates 3 :lookups 1 :quarantined [{:name 'bad-a}]}}
              {:spec 'a :suggestion {:none "none"}
               :reuse {:spec 'a :candidates 3 :lookups 1 :quarantined [{:name 'bad-a}]}}
              {:spec 'b :suggestion {:lemma '(lemma l true)}
               :reuse {:spec 'b :candidates 2 :lookups 1 :quarantined []}}]
        metrics (#'writ.bench/reuse-metrics rows)]
    (is (= {'used 1 'used-other 1} (:citations metrics)))
    (is (= 5 (:candidates metrics)))
    (is (= [{:name 'bad-a}] (:quarantined metrics)))))

(deftest a-reuse-comparison-uses-equal-workloads-on-tuning-and-held-out-corpora
  (let [result (bench/reuse-comparison '[writ.spec-demo.index-spec]
                                       '[writ.spec-demo.walk-spec]
                                       {:jobs 1 :suggest {:budget 1}})
        tune (:tune result)
        keys-of (fn [arm] (set (map (juxt :spec :law) (:rows arm))))]
    (is (seq (keys-of (:baseline tune))))
    (is (= {:budget 1 :reuse false} (get-in tune [:baseline :options :suggest])))
    (is (= {:budget 1 :reuse true} (get-in tune [:reuse :options :suggest])))
    (is (= (keys-of (:baseline tune)) (keys-of (:reuse tune))))
    (is (:same-workload? tune))
    (is (:same-workload? (:held-out result)))
    (is (contains? tune :compare))
    (is (contains? (:held-out result) :compare))
    (is (map? (get-in tune [:reuse :metrics :citations])))
    (is (vector? (get-in tune [:reuse :metrics :quarantined])))
    (let [report (bench/reuse-report result)]
      (is (re-find #"tune: \d+ gained, \d+ lost" report))
      (is (re-find #"held-out: \d+ gained, \d+ lost" report))
      (is (re-find #"candidates" report)))))
