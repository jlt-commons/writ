(ns writ.throws-test
  "Laws about when code throws, and laws quantified over fns."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.string :as str]
            [clojure.test.check.generators :as gen]
            [writ.spec :as spec]))

(defn- has? [r s] (str/includes? (:message r) s))

(defn- law-result [report nm]
  (first (filter #(= nm (:law %)) (:laws report))))

(deftest throws-and-fn-laws-hold-of-the-code
  (let [r (spec/check 'writ.spec-demo.ref-spec {:seed 42})]
    (is (:ok r) (:message r))
    (is (#{:proved :tested} (:status (law-result r 'what-is-kept-passes))))
    (is (= :tested (:status (law-result r 'reading-past-the-end-throws))))))

(deftest code-that-does-not-throw-where-it-must-fails
  (let [r (spec/check 'writ.spec-demo.ref-spec {:seed 42 :target 'writ.spec-demo.ref-lenient})]
    (is (not (:ok r)))
    (is (= :failed (:status (law-result r 'reading-past-the-end-throws))))))

(deftest a-law-over-fns-shows-the-fn-that-breaks-it
  (let [r (spec/check 'writ.spec-demo.ref-spec {:seed 42 :target 'writ.spec-demo.ref-inverted})]
    (is (not (:ok r)))
    (is (= :failed (:status (law-result r 'what-is-kept-passes))))
    (testing "a generated fn prints as the calls it answered"
      (is (re-find #"p\s+= \(fn \{\d+ (true|false)" (:message r)) (:message r)))))

(deftest a-type-error-is-not-a-throw-of-the-code
  (let [r (spec/check 'writ.spec-demo.ref-misuse-spec {:seed 42 :adequacy false})]
    (is (= :failed (:status (law-result r 'a-negative-index-throws))))
    (is (has? r "`at` argument 2 (i) expects Nat, got -1"))))

(deftest a-generated-fn-answers-the-same-each-time
  (let [fs (spec/sample '(-> Nat Nat) {} 30)]
    (is (every? ifn? fs))
    (is (every? #(= (% 3) (% 3)) fs))
    (is (every? nat-int? (map #(% 5) fs)))
    (is (< 1 (count (distinct (map #(% 7) fs)))) "different fns give different answers")))

(deftest a-generated-fn-takes-many-arguments-and-replays
  (let [g (#'spec/fn-gen (gen/return 0))
        f (gen/generate g 10 1)]
    (is (= 0 (f 1 2 3 4 5 6 7 8))))
  (let [g (#'spec/fn-gen gen/nat)
        a (gen/generate g 10 7), b (gen/generate g 10 7)]
    (is (= (a inc) (b dec)) "a fn argument answers as any fn does, run to run")))

(deftest a-throw-inside-a-nested-lazy-seq-is-a-throw
  (is (spec/throws? [(map #(/ 1 %) [1 0])]))
  (is (spec/throws? {:k (map #(/ 1 %) [0])}))
  (is (not (spec/throws? [(map inc [1 2])]))))
