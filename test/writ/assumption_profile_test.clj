(ns writ.assumption-profile-test
  (:require [clojure.edn :as edn]
            [clojure.test :refer [deftest is testing]]
            [writ.bundle :as bundle]
            [writ.canonical :as canonical]
            [writ.spec :as spec]))

(defn- law-result [report name]
  (first (filter #(= name (:law %)) (:laws report))))

(deftest laws-report-only-the-assumptions-they-use
  (let [r (spec/check 'writ.spec-demo.slug-spec {:seed 42 :cache false :parallel false})]
    (is (:ok r) (:message r))
    (is (contains? (set (:assumptions-used (law-result r 'cleaning-twice-is-cleaning-once)))
                   "assume.writ.spec-demo.slug-spec/trim-is-idempotent"))
    (is (contains? (set (:assumptions-used (law-result r 'padding-is-ignored)))
                   "assume.writ.spec-demo.slug-spec/trim-drops-padding"))
    (is (= #{"assume.clojure.string/trim" "assume.clojure.string/lower-case"}
           (set (:assumptions-used (law-result r 'a-string-has-its-own-slug)))))
    (is (not-any? #{"assume.writ.spec-demo.slug-spec/trim-drops-padding"}
                  (:assumptions-used (law-result r 'cleaning-twice-is-cleaning-once))))))

(deftest composed-laws-inherit-component-assumptions
  (let [r (spec/check 'writ.spec-demo.slug-user-spec {:seed 42 :cache false :parallel false :adequacy false})]
    (is (:ok r) (:message r))
    (is (contains? (set (:assumptions-used (law-result r 'answering-is-idempotent)))
                   "assume.writ.spec-demo.slug-spec/trim-is-idempotent"))
    (is (contains? (set (:assumptions-used (law-result r 'answering-thrice-is-idempotent)))
                   "assume.writ.spec-demo.slug-spec/trim-is-idempotent"))))

(deftest attestation-compares-law-assumption-closures
  (let [record (::spec/record (spec/check 'writ.spec-demo.slug-spec
                                          {:seed 42 :cache false :parallel false}))
        before (update record :laws
                       (fn [laws]
                         (mapv (fn [law]
                                 (if (= 'cleaning-twice-is-cleaning-once (:law law))
                                   (assoc law :assumptions-used [])
                                   law))
                               laws)))
        result (spec/attest before record)]
    (is (not (:ok result)))
    (is (some #(and (= 'cleaning-twice-is-cleaning-once (:law %))
                    (= :assumptions-added (:what %)))
              (:weakened result)))))

(deftest an-unused-assumption-does-not-weaken-a-spec
  (let [record (::spec/record (spec/check 'writ.spec-demo.slug-unused-spec
                                          {:seed 42 :cache false :parallel false :adequacy false}))
        before (-> record
                   (update :assumptions
                           (fn [assumptions]
                             (vec (remove #(= 'clojure.string/starts-with? (:fn %)) assumptions))))
                   (update :obligations
                           (fn [obligations]
                             (vec (remove #(= "assume.clojure.string/starts-with?" (:id %))
                                          obligations)))))]
    (is (:ok (spec/attest before record))
        (pr-str (spec/attest before record)))))

(deftest bundle-verification-checks-assumption-profiles
  (let [path (str ".target/assumption-profile-" (System/nanoTime) ".edn")
        report (spec/check 'writ.spec-demo.slug-spec
                           {:seed 42 :cache false :parallel false :bundle path})
        value (edn/read-string (slurp path))]
    (is (:ok report) (:message report))
    (is (:ok (bundle/verify value)))
    (let [tampered (assoc value :id nil)
          tampered (assoc-in tampered [:laws 0 :assumptions-used] [])
          tampered (assoc tampered :id (canonical/content-id (dissoc tampered :id)))
          result (bundle/verify tampered)]
      (is (not (:ok result)))
      (is (= :assumptions-mismatch (:error result))))))

(deftest bundle-context-cannot-launder-assumptions
  (let [path (str ".target/assumption-laundering-" (System/nanoTime) ".edn")
        _ (spec/check 'writ.spec-demo.slug-spec
                      {:seed 42 :cache false :parallel false :bundle path})
        value (edn/read-string (slurp path))
        tampered (-> value
                     (update :context dissoc :assumption-contracts :assumption-lemmas :spec-ns)
                     (update :laws (fn [laws] (mapv #(assoc % :assumptions-used []) laws))))
        tampered (assoc tampered :id (canonical/content-id (dissoc tampered :id)))
        result (bundle/verify tampered)]
    (is (not (:ok result)))
    (is (= :assumptions-mismatch (:error result)))))

(deftest trusted-return-signatures-are-profiled-and-attested
  (let [r (spec/check 'writ.spec-demo.slug-spec
                      {:seed 42 :cache false :parallel false})
        law (law-result r 'a-string-has-its-own-slug)]
    (is (contains? (set (:assumptions-used law)) "assume.clojure.string/trim"))
    (let [record (::spec/record r)
          before (update record :assumptions
                         (fn [assumptions]
                           (mapv (fn [a]
                                   (if (= 'clojure.string/trim (:fn a))
                                     (assoc a :sig '[String -> (Opt String)])
                                     a))
                                 assumptions)))
          result (spec/attest before record)]
      (is (not (:ok result)))
      (is (some #(and (= 'clojure.string/trim (:fn %))
                      (= :restated (:what %)))
                (:weakened result))))))
