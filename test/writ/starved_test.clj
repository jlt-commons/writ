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
    (let [r (spec/check 'writ.spec-demo.span-count-spec {:seed seed :target 'writ.spec-demo.span-naive :prove false})]
      (is (= :failed (:status (law-result r 'overlap-is-a-shared-unit))) (str "seed " seed))))
  (let [l (law-result (spec/check 'writ.spec-demo.span-count-spec {:seed 1}) 'overlap-is-a-shared-unit)]
    (is (= :tested (:status l)))
    (is (< 100 (:trials l)))))

(deftest a-failure-in-the-extra-trials-replays-from-its-seed
  (let [miss? #(= :tested (:status (law-result (spec/check 'writ.spec-demo.span-count-spec
                                                             {:seed % :target 'writ.spec-demo.span-naive
                                                              :more-trials false})
                                               'overlap-is-a-shared-unit)))
        s (first (filter miss? (range 1 40)))
        l (law-result (spec/check 'writ.spec-demo.span-count-spec {:seed s :target 'writ.spec-demo.span-naive})
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

;; --- a unit between bounds --------------------------------------------------------

(deftest an-exists-over-bounds-is-proved
  (let [r (spec/check 'writ.spec-demo.span-exists-spec {:seed 1})]
    (is (:ok r) (:message r))
    (is (= :proved (:status (law-result r 'overlap-means-a-shared-unit))))
    (is (= :proved (:status (law-result r 'a-shared-unit-means-overlap))))))

(deftest an-exists-over-bounds-is-refuted-by-the-solver
  ;; one trial: the tests almost never meet it, and the solver always does
  (doseq [seed [1 2 3 4 5]]
    (let [r (spec/check 'writ.spec-demo.span-exists-spec
                        {:seed seed :trials 1 :target 'writ.spec-demo.span-naive :more-trials false})
          l (law-result r 'overlap-means-a-shared-unit)]
      (is (= :failed (:status l)) (str "seed " seed))
      (is (= :solver (:found-by l)) (str "seed " seed)))))

;; --- a refinement built to fit ----------------------------------------------------

(deftest a-refinement-with-a-build-is-generated-through-it
  (let [r (spec/check 'writ.spec-demo.receipt-spec {:seed 1})]
    (is (:ok r) (:message r))))

(deftest a-refinement-a-random-value-rarely-meets-starves-without-one
  (let [r (spec/check 'writ.spec-demo.receipt-unbuilt-spec {:seed 1})]
    (is (not (:ok r)))
    (is (has? r "could not generate a value of refinement `Receipt`"))
    (is (has? r "{:build f}"))))

(deftest a-build-must-name-a-fn
  (is (thrown-with-msg? Exception #"\{:build f\}"
        (macroexpand-1 '(writ.spec/refine R [x Nat] (pos? x) {:build 3})))))

;; --- a hypothesis a test seldom meets ---------------------------------------------

(deftest a-rare-hypothesis-gets-more-trials-before-it-fails
  (let [law 'back-to-back-spans-of-one-length-overlap-where-they-share-a-unit
        starved? #(:no-hypothesis (law-result (spec/check 'writ.spec-demo.span-rare-spec
                                                          {:seed % :more-trials false :adequacy false})
                                              law))
        s (first (filter starved? (range 1 60)))
        r (spec/check 'writ.spec-demo.span-rare-spec {:seed s :adequacy false})
        l (law-result r law)]
    (is (some? s) "some seed meets the hypothesis in none of the first hundred")
    (is (= :tested (:status l)) (:message r))
    (is (pos? (:held l)))))

(deftest a-law-whose-hypothesis-seldom-held-is-called-thin
  (let [r (spec/check 'writ.spec-demo.span-rare-spec {:seed 1 :adequacy false})]
    (is (has? r "is thinly tested: its hypothesis held in"))))

;; --- the code's numbers, in a built value -----------------------------------------

(deftest a-built-value-meets-the-codes-boundaries
  (doseq [seed [1 2 3]]
    (let [r (spec/check 'writ.spec-demo.lending-spec
                        {:seed seed :target 'writ.spec-demo.lending-lax :more-trials false :prove false})
          l (law-result r 'owing-less-than-the-block-may-borrow)]
      (is (= :failed (:status l)) (str "seed " seed ": " (:message r)))
      (is (= 500 (get-in l [:counterexample 'm :fines]))))))

(deftest a-computed-term-is-tried-at-its-boundary
  (doseq [seed [1 2 3]]
    (let [r (spec/check 'writ.spec-demo.owing-spec
                        {:seed seed :trials 1 :more-trials false :target 'writ.spec-demo.owing-lax})
          l (law-result r 'owing-less-than-500-and-not-banned-may-borrow)]
      (is (= :failed (:status l)) (str "seed " seed ": " (:message r)))
      (is (= :solver (:found-by l))))))

;; --- a mutant that survives: the data, or the laws -------------------------------

(defn- mutants-of [r f]
  (first (filter #(= f (:fn %)) (:rejected r))))

(deftest a-mutant-told-apart-only-past-the-generators-reach-is-tried-there
  (let [r (spec/check 'writ.spec-demo.bulk-spec {:seed 42 :cache false :adequacy :mutants})]
    (is (:ok r) (:message r))
    (is (some #(and (= :mutant (:kind %)) (str/includes? (:desc %) "5000"))
              (:rejected (mutants-of r 'price)))
        (pr-str (mutants-of r 'price)))))

(deftest a-mutant-no-law-tells-apart-is-a-gap-in-the-laws
  (let [r (spec/check 'writ.spec-demo.bulk-weak-spec {:seed 42 :cache false :adequacy :mutants})]
    (is (not (:ok r)))
    (is (has? r "no law tells it apart, even run there"))))

;; --- each comparison of a law, both ways ------------------------------------------

(deftest a-comparison-the-trials-never-turned-is-turned-by-the-solver
  ;; one trial, so only the solver turns the comparison
  (doseq [seed [1 2 3]]
    (let [r (spec/check 'writ.spec-demo.spend-spec
                        {:seed seed :trials 1 :more-trials false :target 'writ.spec-demo.spend-open :prove false})
          l (law-result r 'spending-stays-within-the-limit)]
      (is (= :tested (:status l)) "the tests alone pass it"))
    (let [r (spec/check 'writ.spec-demo.spend-spec
                        {:seed seed :trials 1 :more-trials false :target 'writ.spec-demo.spend-open})
          l (law-result r 'spending-stays-within-the-limit)]
      (is (= :failed (:status l)) (str "seed " seed ": " (:message r)))
      (is (= :solver (:found-by l))))))

(deftest a-comparison-seen-one-way-is-reported
  (let [r (spec/check 'writ.spec-demo.spend-freq-spec {:seed 1})]
    (is (has? r "was never false in"))))

(deftest extra-trials-stop-once-each-comparison-went-both-ways
  (let [l (law-result (spec/check 'writ.spec-demo.spend-spec {:seed 1}) 'spending-stays-within-the-limit)]
    (is (= :tested (:status l)))
    (is (< (:trials l) 1000))))

;; --- which rule a value breaks ----------------------------------------------------

(deftest a-value-out-of-its-refinement-is-told-which-rule-it-breaks
  (let [r (spec/check 'writ.spec-demo.shelf-q-spec {:seed 1 :target 'writ.spec-demo.shelf-q-uncounted})]
    (is (not (:ok r)))
    (is (has? r "it breaks (= (:loans m) (lent-to l (:id m)))") (:message r))
    (is (has? r "at (:members l) key 0, m = {:id 0, :loans 0}") (:message r))))

(deftest the-step-that-broke-a-value-is-reported-first-and-once
  (let [r (spec/check 'writ.spec-demo.shelf-q-spec {:seed 1 :target 'writ.spec-demo.shelf-q-uncounted})
        m (:message r)
        i (str/index-of m "`lend` returns values outside Lib")]
    (is (some? i) m)
    (is (< i (or (str/index-of m "law `") Long/MAX_VALUE)) "before any law's own failure")
    (is (has? r "laws that fail because of it: desk:lib:lend, lending-marks-the-copy") m)
    (is (= 1 (count (re-seq #"it breaks \(= \(:loans m\)" m))) "the broken rule once")))

;; --- frames on paths named by the step's arguments --------------------------------

(deftest a-path-frame-keeps-everything-but-the-paths-it-names
  (let [r (spec/check 'writ.spec-demo.shelf-q-frame-spec {:seed 1})]
    (is (:ok r) (:message r)))
  (let [r (spec/check 'writ.spec-demo.shelf-q-frame-spec {:seed 1 :target 'writ.spec-demo.shelf-q-meddle})]
    (is (not (:ok r)))
    (is (= :failed (:status (law-result r 'desk:lib:lend:frame))) (:message r))))

(deftest a-path-frame-names-only-the-steps-arguments
  (is (thrown-with-msg? Exception #"\(arg i\)"
        (macroexpand-1 '(writ.spec/graph g {:states {:a A} :edges {:a {[f Nat] {:to #{:a} :changes [[:k (arg 3)]]}}}})))))

;; --- a guard named once, for the graph and the laws -------------------------------

(deftest a-guard-may-name-a-spec-fn-the-laws-use-too
  (let [r (spec/check 'writ.spec-demo.shelf-q-guard-spec {:seed 1})
        names (set (map :law (:laws r)))]
    (is (:ok r) (:message r))
    (is (contains? names 'desk:lib:lend:refused))
    (is (contains? names 'desk:lib:lend:when.1) "the helper's own clauses, each its own law")))

;; --- a law that tells no stand-in apart -------------------------------------------

(deftest a-law-that-rejects-no-stand-in-is-named
  (let [r (spec/check 'writ.spec-demo.typey-spec {:seed 1})]
    (is (has? r "law `isort-gives-a-seq` tells none of"))
    (is (has? r "law `isort-gives-nats` tells none of"))
    (is (not (has? r "law `sorting:unsorted:isort` tells none of")) "a graph's own laws are not named"))
  (is (not (has? (spec/check 'writ.spec-demo.sort-spec {:seed 42}) "tells none of"))))

;; --- examples beside the laws -----------------------------------------------------

(deftest an-example-the-laws-do-not-pin-down-is-a-gap
  (let [r (spec/check 'writ.spec-demo.bulk-example-spec {:seed 42})]
    (is (not (:ok r)))
    (is (= :evaluated (:status (law-result r 'example:price:1))))
    (is (has? r "except at (price 6000)") (:message r)))
  (let [r (spec/check 'writ.spec-demo.bulk-example-full-spec {:seed 42})]
    (is (:ok r) (:message r))))

(deftest an-example-checks-the-code
  (let [r (spec/check 'writ.spec-demo.bulk-example-full-spec {:seed 42 :target 'writ.spec-demo.bulk-off})]
    (is (= :failed (:status (law-result r 'example:price:1))))))

;; --- a model of the state, one law per edge ---------------------------------------

(deftest each-edge-commutes-with-the-model
  (let [r (spec/check 'writ.spec-demo.twolist-spec {:seed 1})]
    (is (:ok r) (:message r))
    (is (law-result r 'queue:q:enqueue:model))
    (is (law-result r 'queue:q:dequeue:model)))
  (let [r (spec/check 'writ.spec-demo.twolist-spec {:seed 1 :target 'writ.spec-demo.twolist-wrong-end})]
    (is (= :failed (:status (law-result r 'queue:q:dequeue:model))) (:message r))))

;; --- a spec held to a baseline ----------------------------------------------------

(deftest a-spec-weaker-than-its-baseline-fails
  (let [path "test/writ/spec_demo/sort_baseline.edn"]
    (try
      (spec/check 'writ.spec-demo.sort-held-spec {:seed 42 :record path})
      (let [r (spec/check 'writ.spec-demo.sort-held-spec {:seed 42})]
        (is (:ok r) (:message r)))
      (let [r (spec/check 'writ.spec-demo.sort-loosened-spec {:seed 42})]
        (is (not (:ok r)))
        (is (has? r "weaker than its baseline"))
        (is (has? r "law `permutation` is removed"))
        (is (has? r "the ann of `insert` is changed")))
      (finally (clojure.java.io/delete-file path true)))))

(deftest a-missing-baseline-fails-and-says-how-to-make-one
  (let [r (spec/check 'writ.spec-demo.sort-held-spec {:seed 42})]
    (is (not (:ok r)))
    (is (has? r ":record"))))

;; --- ranges as sets ---------------------------------------------------------------

(deftest a-law-over-ranges-as-sets-is-proved
  (let [r (spec/check 'writ.spec-demo.span-spec {:seed 1})]
    (is (= :proved (:status (law-result r 'overlap-is-a-shared-unit))) (:message r)))
  (doseq [seed [1 2 3]]
    (let [l (law-result (spec/check 'writ.spec-demo.span-spec
                                    {:seed seed :trials 1 :more-trials false :target 'writ.spec-demo.span-naive})
                        'overlap-is-a-shared-unit)]
      (is (= :failed (:status l)))
      (is (= :solver (:found-by l))))))

;; --- a step of several guarded cases ----------------------------------------------

(deftest each-case-of-a-step-has-its-own-laws
  (let [r (spec/check 'writ.spec-demo.bank-spec {:seed 1})
        names (set (map :law (:laws r)))]
    (is (:ok r) (:message r))
    (is (every? names '[bank:open:withdraw#1 bank:open:withdraw#2
                        bank:open:withdraw#1:frame bank:open:withdraw#2:frame
                        bank:open:withdraw:cases])
        (pr-str (sort names)))))

(deftest a-case-is-held-to-its-own-frame
  (let [r (spec/check 'writ.spec-demo.bank-spec {:seed 1 :target 'writ.spec-demo.bank-greedy})]
    (is (= :failed (:status (law-result r 'bank:open:withdraw#1:frame))) (:message r))
    (is (not= :failed (:status (law-result r 'bank:open:withdraw#2:frame))))))

(deftest cases-that-overlap-are-shown-where
  (let [r (spec/check 'writ.spec-demo.bank-overlap-spec {:seed 1})]
    (is (= :failed (:status (law-result r 'bank:open:withdraw:cases))) (:message r))
    (is (has? r "cases 1 and 2 of withdraw from open both hold"))))
