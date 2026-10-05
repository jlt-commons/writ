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

(deftest a-scalar-of-a-law-is-now-and-then-one-its-other-values-hold
  ;; drawn apart, an `id` is rarely a key of the queue drawn beside it
  (let [r (spec/check 'writ.spec-demo.jobs-spec {:seed 7 :adequacy false :more-trials false :cache false})
        l (law-result r 'a-due-job-named-is-taken)]
    (is (= :tested (:status l)) (:message r))
    (is (<= 20 (- (:trials l) (:discarded l))) (pr-str l))))

(deftest a-comparison-under-a-let-is-taken-with-it
  ;; run with the law's variables alone, `start` would be unbound
  (let [{:keys [atoms]} (#'spec/law-atom-parts
                          '(=> (some? (f x)) (let [[room start] (f x)] (or (<= x start) (= room 0))))
                          '[x])]
    (is (some #{'(let [[room start] (f x)] (<= x start))} atoms) (pr-str atoms))
    (is (not-any? #{'(<= x start)} atoms) (pr-str atoms))))

(deftest a-contains-test-guards-the-read-it-makes-safe
  (let [r (spec/check 'writ.spec-demo.gate-spec {:seed 7 :adequacy false})]
    ;; and a for's own tests, (chunked-seq? ...), are no test of the code
    (is (not-any? #(re-find #"__\d+" %) (:one-way-tests r)) (pr-str (:one-way-tests r)))
    (is (not-any? #(re-find #"`holder`" %) (:one-way-tests r)) (pr-str (:one-way-tests r)))))

(deftest a-missing-tie-break-is-caught-where-the-tie-decides
  ;; five random trials, none extra: the tie that shows the wrong order
  ;; comes from the inputs found by turning the sort's ties around
  (doseq [sd [1 2 3]]
    (let [opts {:seed sd :adequacy false :cache false :trials 5 :more-trials false}
          bad (spec/check 'writ.spec-demo.lots-spec (assoc opts :target 'writ.spec-demo.lots-untied))
          good (spec/check 'writ.spec-demo.lots-spec opts)
          l (law-result bad 'the-earliest-then-the-lowest-id)]
      (is (= :failed (:status l)) (str "seed " sd ": " (:message bad)))
      (is (= :tie (:found-by l)) (str "seed " sd))
      (is (str/includes? (:message bad) "where the order of tied items decides"))
      (is (:ok good) (str "seed " sd ": " (:message good))))))

(deftest a-tie-break-no-law-pins-is-a-gap
  ;; with no law about it, the order of tied lots is a stand-in no law rejects
  (let [r (spec/check 'writ.spec-demo.lots-loose-spec {:seed 7})]
    (is (some #(str/includes? % "puts tied items of") (mapcat :survivors (:gaps r))) (:message r))))
