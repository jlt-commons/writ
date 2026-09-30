(ns writ.starved-test
  "Conditions random values rarely meet: a law's hypothesis, a guard on a
  step a run takes. writ looks for values that meet them rather than
  failing, or passing, on what the draws happened to be."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.string :as str]
            [writ.spec :as spec]))

(defn- law-result [report nm]
  (first (filter #(= nm (:law %)) (:laws report))))

(defn- has? [r s] (str/includes? (:message r) s))

;; --- a hypothesis no generated input meets ----------------------------------------

(deftest a-proved-law-stands-when-the-solver-meets-its-hypothesis
  (doseq [seed [1 2 3 42]]
    (let [r (spec/check 'writ.spec-demo.gap-spec {:seed seed})]
      (is (:ok r) (:message r))
      (is (= :proved (:status (law-result r 'far-apart))))
      (is (has? r "its hypothesis held at")))))

(deftest code-wrong-only-where-the-hypothesis-holds-is-refuted-by-the-solver
  (let [r (spec/check 'writ.spec-demo.gap-spec {:seed 42 :target 'writ.spec-demo.gap-far})
        l (law-result r 'far-apart)]
    (is (not (:ok r)))
    (is (= :failed (:status l)))
    (is (= :solver (:found-by l)))
    (is (> (get-in l [:counterexample 'a]) 90))
    (is (not (has? r "the hypothesis never held")))))

;; --- a guard a random argument rarely meets ---------------------------------------

(deftest a-run-looks-for-an-argument-its-guard-takes
  (doseq [seed [1 2 3 42 1000]]
    (let [r (spec/check 'writ.spec-demo.checkout-spec {:seed seed})]
      (is (:ok r) (str "seed " seed ": " (:message r))))))

(deftest runs-are-walked-toward-a-final-state-the-random-ones-missed
  (doseq [seed [1 2 3 42 1000]]
    (let [r (spec/check 'writ.spec-demo.checkout-cancel-spec {:seed seed})]
      (is (:ok r) (str "seed " seed ": " (:message r))))))

(deftest a-guard-that-refuses-every-run-is-named
  (let [r (spec/check 'writ.spec-demo.checkout-locked-spec {:seed 42})]
    (is (not (:ok r)))
    (is (has? r "no run of 10 reached :shipped"))
    (is (has? r "the guard of pay from :placed refused"))))

;; --- a law the prover cannot prove ------------------------------------------------

(deftest a-law-only-tested-gets-more-trials
  (doseq [seed (range 1 11)]
    (let [r (spec/check 'writ.spec-demo.span-spec {:seed seed :target 'writ.spec-demo.span-naive})]
      (is (= :failed (:status (law-result r 'overlap-is-a-shared-unit))) (str "seed " seed))))
  (let [l (law-result (spec/check 'writ.spec-demo.span-spec {:seed 1}) 'overlap-is-a-shared-unit)]
    (is (= :tested (:status l)))
    (is (= 1000 (:trials l)))))

(deftest a-failure-in-the-extra-trials-replays-from-its-seed
  (let [miss? #(= :tested (:status (law-result (spec/check 'writ.spec-demo.span-spec
                                                             {:seed % :target 'writ.spec-demo.span-naive
                                                              :more-trials false})
                                               'overlap-is-a-shared-unit)))
        s (first (filter miss? (range 1 40)))
        l (law-result (spec/check 'writ.spec-demo.span-spec {:seed s :target 'writ.spec-demo.span-naive})
                      'overlap-is-a-shared-unit)]
    (is (some? s) "some seed misses it in the first hundred trials")
    (is (= :failed (:status l)))
    (is (not (miss? (:seed l))) "its seed finds it in the first hundred")))

;; --- a rule across an index's records ---------------------------------------------

(deftest an-index-refinement-is-built-to-fit
  (let [t0 (System/currentTimeMillis)
        r (spec/check 'writ.spec-demo.slots-spec {:seed 2 :more-trials false})]
    (is (:ok r) (:message r))
    (is (< (- (System/currentTimeMillis) t0) 30000) "built, not filtered for")))
