(ns writ.proof-test
  "The proof namespace: lemmas and hints the agent writes to get a spec's
  laws proved, kept apart from the spec, which is the contract.  A lemma
  is a law about the code like any other, so it must hold and be proved;
  it helps prove the spec's laws, but never counts as one of them."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.string :as str]
            [writ.spec :as spec]))

(defn- law-result [report nm]
  (first (filter #(= nm (:law %)) (:laws report))))

(deftest without-its-lemma-a-law-stays-unproved
  (let [r (spec/check 'writ.spec-demo.sort-lemma-spec {:seed 42 :proof false})]
    (is (not (:ok r)))
    (is (= :unproved (:status (law-result r 'sorted))))))

(deftest a-lemma-from-the-proof-namespace-gets-it-proved
  (let [r (spec/check 'writ.spec-demo.sort-lemma-spec {:seed 42})]
    (is (:ok r) (:message r))
    (is (= :proved (:status (law-result r 'sorted))))
    (is (= ['insert-keeps-sorted] (:lemmas (law-result r 'sorted))))
    (testing "the lemma is reported apart, and does not count as a law of the spec"
      (is (= [{:lemma 'insert-keeps-sorted :status :proved}]
             (mapv #(select-keys % [:lemma :status]) (:lemmas r))))
      (is (= 3 (:laws (:proof r))))
      (is (str/includes? (:message r) "lemma `insert-keeps-sorted` proved")))))

(deftest a-false-lemma-fails-the-check
  (let [r (spec/check 'writ.spec-demo.sort-lemma-spec
                      {:seed 42 :proof 'writ.spec-demo.sort-false-lemma-proof})]
    (is (not (:ok r)))
    (is (= :failed (:status (first (:lemmas r)))))
    (is (str/includes? (:message r) "lemma `insert-keeps-length` fails for"))))

(deftest proof-forms-are-checked-when-they-load
  (let [err (fn [form] (try (macroexpand-1 form) nil (catch Throwable e (ex-message e))))]
    (is (str/includes? (err '(writ.spec/hint sorted [:induct xs]))
                       "`hint sorted` takes a map"))
    (is (str/includes? (err '(writ.spec/hint sorted {:strategy :magic}))
                       ":strategy must be one of"))
    (is (str/includes? (err '(writ.spec/hint sorted {:color :red}))
                       "unknown keys"))))

(deftest the-tree-holds-a-sorted-set-is-proved-from-its-proof-namespace
  (let [r (spec/check 'writ.spec-demo.tree-spec {:seed 42 :cache false})
        l (law-result r 'holds-a-sorted-set)]
    (is (:ok r) (:message r))
    (is (= :proved (:status l)) (pr-str l))
    (is (= ['build-lists] (:lemmas l)))
    (testing "every lemma is proved, those about clojure.core alone too"
      (is (every? #(= :proved (:status %)) (:lemmas r)) (pr-str (:lemmas r)))
      (is (= :proved (:status (first (filter #(= 'none-below (:lemma %)) (:lemmas r)))))))
    (testing "the fold is proved with its accumulator varying in the hypothesis"
      (is (re-find #"by induction on xs"
                   (:proof (first (filter #(= 'build-lists (:lemma %)) (:lemmas r)))))))))

(deftest a-broken-tree-is-not-proved-a-sorted-set
  (doseq [target '[writ.spec-demo.tree-mirror writ.spec-demo.tree-bad-build]]
    (let [r (spec/check 'writ.spec-demo.tree-spec {:seed 42 :cache false :target target})]
      (is (not= :proved (:status (law-result r 'holds-a-sorted-set))) (str target))
      (is (not-any? :prover-bug (concat (:laws r) (:lemmas r))) (str target)))))

(deftest a-vary-hint-is-checked-when-it-loads
  (let [err (fn [form] (try (macroexpand-1 form) nil (catch Throwable e (ex-message e))))]
    (is (str/includes? (err '(writ.spec/hint fold {:vary acc})) ":vary is a vector"))
    (is (str/includes? (err '(writ.spec/hint fold {:induct xs :vary [xs]}))
                       "cannot vary in its own hypothesis"))
    (is (nil? (err '(writ.spec/hint fold {:induct xs :vary [acc]}))))))

(deftest a-proof-found-once-is-reused
  (let [dir (str ".target/writ-cache-test-" (System/currentTimeMillis))
        first-run (spec/check 'writ.spec-demo.court-spec {:seed 42 :cache-dir dir})
        again (spec/check 'writ.spec-demo.court-spec {:seed 42 :cache-dir dir})
        proved (fn [r] (set (map :law (filter #(= :proved (:status %)) (:laws r)))))]
    (is (:ok again) (:message again))
    (is (seq (proved first-run)))
    (is (= (proved first-run) (proved again)))
    (testing "the second check finds its proofs in the cache"
      (is (every? :cached (filter #(= :proved (:status %)) (:laws again))))
      (is (not-any? :cached (:laws first-run))))
    (testing "the contracts are kept apart from the laws, keyed on the code"
      (let [f (io/file dir "contracts--writ.spec-demo.court.edn")
            c (edn/read-string (slurp f))]
        (is (.exists f))
        (is (contains? (set (map :name (:rules c))) 'move%contract))))
    (testing "another target has a cache of its own"
      (let [other (spec/check 'writ.spec-demo.court-spec {:seed 42 :cache-dir dir :target 'writ.spec-demo.court-open})]
        (is (not-any? :cached (:laws other)))))
    (testing "without the cache, every proof is found again"
      (is (not-any? :cached (:laws (spec/check 'writ.spec-demo.court-spec {:seed 42 :cache false})))))))
