(ns writ.bundle-test
  (:require [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.test :refer [deftest is testing]]
            [writ.bundle :as bundle]
            [writ.canonical :as canonical]
            [writ.proposition :as proposition]
            [writ.spec :as spec]))

(deftest canonical-identities-are-deterministic-and-injective
  (is (= (canonical/content-id {:a 1 :b #{2 3}})
         (canonical/content-id {:b #{3 2} :a 1})))
  (is (not= (canonical/content-id 1) (canonical/content-id "1")))
  (is (not= (canonical/content-id '(1 2)) (canonical/content-id [1 2])))
  (is (not= (canonical/content-id 1/2) (canonical/content-id 0.5)))
  (is (= (canonical/content-id "é漢字") (canonical/content-id "é漢字")))
  (is (not= (canonical/content-id "é") (canonical/content-id "e")))
  (is (= (canonical/content-id (cons 1 '(2))) (canonical/content-id '(1 2))))
  (is (= [55357 56832] (get-in (canonical/canonical "😀") [:root 2])))
  (is (not= (canonical/content-id (float 1.0)) (canonical/content-id (double 1.0))))
  (is (not= (canonical/content-id 0.0) (canonical/content-id -0.0)))
  (let [shared [1 2]]
    (is (= (canonical/content-id [shared shared])
           (canonical/content-id [[1 2] [1 2]]))))
  (is (not= (canonical/content-id ##NaN) (canonical/content-id ##Inf))))

(defn- temp-path []
  (str ".target/bundle-test-" (System/nanoTime) ".edn"))

(defn- reidentify [value]
  (assoc value :id (canonical/content-id (dissoc value :id))))

(defn- exported []
  (let [path (temp-path)
        report (spec/check 'writ.spec-demo.index-spec
                           {:seed 1 :cache false :parallel false :bundle path})]
    (is (:ok report) (:message report))
    (is (.exists (io/file path)))
    (edn/read-string (slurp path))))

(deftest bundle-output-accepts-a-relative-path
  (let [path (str "bundle-test-" (System/nanoTime) ".edn")]
    (try
      (let [report (spec/check 'writ.spec-demo.index-spec
                               {:seed 1 :cache false :parallel false :bundle path})]
        (is (:ok report) (:message report))
        (is (:ok (bundle/verify path))))
      (finally (.delete (io/file path))))))

(deftest an-exported-proof-bundle-replays-independently
  (let [value (exported)
        result (bundle/verify value)]
    (is (= 1 (:writ.bundle/schema-version value)))
    (is (:ok result) (pr-str result))
    (is (seq (:laws result)))
    (is (every? #(= :replayed (:status %)) (:laws result)))
    (is (pos? (:contracts result)))))

(deftest a-tampered-law-trace-is-rejected-even-with-a-new-id
  (let [value (exported)
        tampered (reidentify
                  (update-in value [:laws 0 :trace]
                             (constantly {:by :not-a-proof})))
        result (bundle/verify tampered)]
    (is (not (:ok result)))
    (is (= :law-rejected (:error result)))))

(deftest a-tampered-contract-trace-is-rejected
  (let [value (exported)
        k (first (keys (get-in value [:contracts :traces])))
        tampered (reidentify
                  (assoc-in value [:contracts :traces k] {:by :not-a-proof}))
        result (bundle/verify tampered)]
    (is (not (:ok result)))
    (is (= :contracts-rejected (:error result)))))

(deftest unknown-cited-lemmas-and-bad-schemas-are-rejected
  (let [value (exported)]
    (testing "an unproved lemma cannot be injected into a law's context"
      (let [tampered (reidentify
                      (update-in value [:laws 0 :args :lemmas]
                                 #(conj (vec %) {:name 'forged/lemma
                                                 :prop '(forall [x Int] (= x x))})))
            result (bundle/verify tampered)]
        (is (not (:ok result)))
        (is (= :unknown-lemma (:error result)))))
    (testing "an unsupported schema is not accepted"
      (is (not (:ok (bundle/verify (assoc value :writ.bundle/schema-version 99)))))))

(deftest malformed-but-identified-bundles-are-rejected
  (is (= :invalid-bundle
         (:error (bundle/verify (reidentify {:writ.bundle/schema-version 1})))))
  (let [value (exported)
        duplicated (reidentify (update value :laws #(conj (vec %) (first %))))]
    (is (= :invalid-bundle (:error (bundle/verify duplicated))))))

(deftest composed-proof-bundles-replay-dependencies
  (let [path (str ".target/composed-bundle-" (System/nanoTime) ".edn")
        report (spec/check 'writ.spec-demo.shop-spec
                           {:seed 1 :cache false :parallel false :bundle path})
        value (edn/read-string (slurp path))
        result (bundle/verify value)]
    (is (:ok report) (:message report))
    (is (seq (:dependencies value)))
    (is (:ok result) (pr-str result))
    (is (= 3 (count (:laws result))))))

(deftest alpha-equivalent-alias-laws-are-checked-references
  (let [value (exported)
        referenced (get-in value [:laws 0])
        alias {:law 'alias/of-first
               :kind :alias
               :of (:law referenced)
               :prop (:prop (:args referenced))
               :assumptions-used []}
        accepted (bundle/verify (reidentify (update value :laws #(conj (vec %) alias))))]
    (is (:ok accepted) (pr-str accepted))
    (let [rejected (bundle/verify
                    (reidentify
                     (update value :laws
                             #(conj (vec %) (assoc alias :law 'alias/unknown :of 'unknown/law)))))]
      (is (not (:ok rejected)))
      (is (= :alias-rejected (:error rejected)))))))

(deftest aliases-accept-renamed-assumption-backed-and-refined-propositions
  (let [path (str ".target/alias-assumptions-" (System/nanoTime) ".edn")
        _ (spec/check 'writ.spec-demo.slug-spec
                      {:seed 42 :cache false :parallel false :bundle path})
        value (edn/read-string (slurp path))
        referenced (get-in value [:laws 0])
        prop (get-in referenced [:args :prop])
        x (first (second prop))
        alias {:law 'alias/renamed :kind :alias :of (:law referenced)
               :prop (proposition/subst-var prop x 'renamed)
               :assumptions-used (:assumptions-used referenced)}]
    (is (:ok (bundle/verify (reidentify (update value :laws #(conj (vec %) alias)))))))
  (let [path (str ".target/alias-refined-" (System/nanoTime) ".edn")
        _ (spec/check 'writ.spec-demo.member-spec
                      {:seed 42 :cache false :parallel false :bundle path})
        value (edn/read-string (slurp path))
        referenced (get-in value [:laws 0])
        alias {:law 'alias/refined :kind :alias :of (:law referenced)
               :prop (get-in referenced [:args :prop])
               :assumptions-used (:assumptions-used referenced)}]
    (is (:ok (bundle/verify (reidentify (update value :laws #(conj (vec %) alias))))))))
