(ns writ.assume-test
  "Assumptions: what a spec takes as given about code writ does not
  check.  An assumed signature types the calls and is checked where the
  fn returns; an assumed law is tested against the real fns on every
  check, and the prover may cite it.  Every report names them."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.string :as str]
            [writ.spec :as spec]))

(defn- has? [r s] (str/includes? (:message r) s))

(defn- law-result [report nm]
  (first (filter #(= nm (:law %)) (:laws report))))

(deftest laws-that-rest-on-assumptions-are-proved
  (let [r (spec/check 'writ.spec-demo.slug-spec {:seed 42})]
    (is (:ok r) (:message r))
    (doseq [l '[cleaning-twice-is-cleaning-once padding-is-ignored a-string-has-its-own-slug
                padded-strings-share-a-slug slugging:raw:clean]]
      (is (= :proved (:status (law-result r l))) (str l ": " (:unproved (law-result r l)))))
    (testing "the report names every assumption and says each held"
      (is (= #{'trim-is-idempotent 'lower-case-is-idempotent 'trim-and-lower-case-commute
               'trim-drops-padding}
             (set (keep :assumption (:assumptions r)))))
      (is (every? #(= :held (:status %)) (:assumptions r)))
      (is (= '#{clojure.string/trim clojure.string/lower-case}
             (set (keep :fn (:assumptions r)))))
      (is (has? r "assumes, tested but not proved"))
      (is (has? r "trim-and-lower-case-commute")))
    (testing "an assumption is not a law of the spec"
      (is (nil? (law-result r 'trim-is-idempotent)))
      (is (not-any? #(contains? #{'trim-is-idempotent 'trim-drops-padding} (:law %)) (:laws r))))))

(deftest without-the-assumptions-the-laws-are-only-tested
  (let [r (spec/check 'writ.spec-demo.slug-bare-spec {:seed 42})]
    (is (:ok r) (:message r))
    (is (= :tested (:status (law-result r 'cleaning-twice-is-cleaning-once))))))

(deftest an-assumption-that-does-not-hold-fails
  (let [r (spec/check 'writ.spec-demo.slug-false-spec {:seed 42})]
    (is (not (:ok r)))
    (is (= :failed (:status (first (filter #(= 'trim-empties (:assumption %)) (:assumptions r))))))
    (is (has? r "assumption `trim-empties` does not hold"))))

(deftest an-assumption-may-not-be-about-the-target
  (let [r (spec/check 'writ.spec-demo.slug-cheat-spec {:seed 42})]
    (is (not (:ok r)))
    (is (has? r "assumption `clean-is-idempotent` calls `clean`, a fn of writ.spec-demo.slug"))))

(deftest an-assumed-signature-is-checked-where-the-fn-returns
  (let [r (spec/check 'writ.spec-demo.slug-liar-spec {:seed 42})]
    (is (not (:ok r)))
    (is (has? r "`clojure.string/trim` returns Nat, but returned"))))

(deftest an-assumed-signature-types-the-calls
  (let [r (spec/check 'writ.spec-demo.slug-spec {:seed 42 :target 'writ.spec-demo.slug-badcall})]
    (is (not (:ok r)))
    (is (has? r "`clojure.string/trim` expects String for argument 1 but is passed Nat"))))

(deftest assumptions-are-obligations-and-in-the-plan
  (let [ids (set (map :id (spec/obligations 'writ.spec-demo.slug-spec)))]
    (is (contains? ids "assume.trim-is-idempotent"))
    (is (contains? ids "assume.clojure.string/trim")))
  (let [p (spec/plan 'writ.spec-demo.slug-spec)]
    (is (str/includes? p "assumes"))
    (is (str/includes? p "clojure.string/trim  [String -> String]"))
    (is (str/includes? p "trim-is-idempotent"))))

(deftest a-new-assumption-weakens-the-spec
  (let [now (::spec/record (spec/check 'writ.spec-demo.slug-spec {:seed 42}))
        before (-> now
                   (update :assumptions (fn [as] (vec (remove #(= 'trim-drops-padding (:assumption %)) as))))
                   (update :obligations (fn [os] (vec (remove #(= "assume.trim-drops-padding" (:id %)) os)))))
        a (spec/attest before now)]
    (is (not (:ok a)))
    (is (some #(and (= 'trim-drops-padding (:assumption %)) (= :added (:what %))) (:weakened a)))
    (is (:ok (spec/attest now now)))))

(deftest an-assumption-names-a-fn-that-exists
  (is (thrown-with-msg? Exception #"`assume` names a fn by its qualified name"
        (macroexpand '(writ.spec/assume trim [String -> String]))))
  (is (thrown-with-msg? Exception #"`assume` takes"
        (macroexpand '(writ.spec/assume str/trim 5)))))

(deftest a-core-fn-outside-the-prover-can-be-assumed
  (let [r (spec/check 'writ.spec-demo.tally-spec {:seed 42 :cache false :require :tested})]
    (is (:ok r) (:message r))
    (is (= :proved (:status (law-result r 'every-value-is-counted))) (str (:unproved (law-result r 'every-value-is-counted))))
    (is (has? r "citing the-counts-add-up"))))
