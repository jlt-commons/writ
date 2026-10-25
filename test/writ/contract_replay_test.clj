(ns writ.contract-replay-test
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.test :refer [deftest is]]
            [writ.book :as book]
            [writ.prove :as prover]
            [writ.spec :as spec]))

(def ^:private forms
  '[(ns c.nums)
    (defn twice [n] (* 2 n))
    (defn down [n] (- n 1))
    (defn total [xs] (if (seq xs) (+ (first xs) (total (rest xs))) 0))
    (defn half-str [s] (str s))])

(defn- contracts [options]
  (let [[defs] (prover/definitions [['c.nums forms]])]
    (prover/prove-contracts
     (merge {:defs defs :tenv {}
             :sigs '{c.nums/twice {:params [Int] :ret Int}
                     c.nums/down {:params [Nat] :ret Nat}
                     c.nums/total {:params [(List Nat)] :ret Nat}
                     c.nums/half-str {:params [Int] :ret Int}}}
            options))))

(deftest contract-traces-replay-without-search
  (let [fresh (contracts {})
        replayed (contracts {:traces (:traces fresh) :replay-only true})]
    (is (= '#{twice%contract down%contract total%contract total%nonneg%contract}
           (set (map :name (:rules fresh)))))
    (is (= (:rules fresh) (:rules replayed)))
    (is (empty? (:replay-errors replayed)))
    (let [rejected (contracts {:traces (zipmap (keys (:traces fresh))
                                               (repeat {:by :not-a-proof}))
                               :replay-only true})]
      (is (empty? (:rules rejected)))
      (is (seq (:replay-errors rejected))))))

(deftest forged-cached-contract-rules-are-not-trusted
  (let [dir (str ".target/contract-replay-test-" (System/nanoTime))
        check #(spec/check 'writ.spec-demo.court-spec
                           {:seed 42 :cache-dir dir :parallel false})
        f (io/file dir "contracts--writ.spec-demo.court.edn")]
    (is (:ok (check)))
    (let [c (edn/read-string (slurp f))]
      (spit f (pr-str (assoc c :rules [] :traces {}))))
    (let [r (check)
          rewritten (edn/read-string (slurp f))]
      (is (:ok r) (:message r))
      (is (seq (:traces rewritten))))))
