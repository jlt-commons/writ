(ns writ.reuse-test
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [writ.reuse :as reuse]
            [writ.spec :as spec]))

(def ^:private context
  {:defs {} :tenv {} :own {}})

(deftest normalized-retrieval-is-alpha-and-rewrite-aware
  (let [proved {:name 'add-zero :prop '(forall [x Int] (= (+ x 0) x))}
        index (reuse/index [proved] context)
        candidates (reuse/candidates index '(forall [y Int] (= y (+ 0 y))) {})]
    (is (= ['add-zero] (mapv :name candidates)))
    (is (every? :reuse/exact candidates))))

(deftest retrieval-is-deterministic-and-policy-aware
  (let [free {:name 'free :prop '(forall [x Int] (= (+ x 0) x))}
        assumed {:name 'assumed :prop '(forall [n Int] (= (+ n 0) n))
                 :assumptions-used ["assume.demo/identity"]}
        unproved {:name 'unproved :prop '(forall [x Int] (= x x)) :status :tested}
        index (reuse/index [assumed unproved free] context)]
    (testing "unproved and disallowed evidence is absent by default"
      (is (= ['free] (mapv :name (reuse/candidates index '(forall [y Int] (= y (+ 0 y))) {})))))
    (testing "an explicitly allowed assumption is included after assumption-free matches"
      (let [candidates (reuse/candidates index '(forall [y Int] (= y (+ 0 y)))
                                         {:allowed-assumptions #{"assume.demo/identity"}})]
        (is (= ['free 'assumed] (mapv :name candidates)))
        (is (= [true true] (mapv :reuse/exact candidates)))))
    (testing "an empty result stays empty"
      (is (empty? (reuse/candidates index '(forall [s String] (= s s)) {}))))))

(deftest unnormalizable-lemmas-are-quarantined-without-hiding-valid-ones
  (let [free {:name 'free :prop '(forall [x Int] (= (+ x 0) x))}
        bad (fn [nm] {:name nm
                      :prop '(forall [x Int] (exists [y Int] (= x y)))})
        index (reuse/index [(bad 'z-bad) free (bad 'a-bad)] context)]
    (is (= ['free] (mapv :name (:entries index))))
    (is (= ['a-bad 'z-bad] (mapv :name (:quarantined index))))
    (is (every? #(= :normalization-failed (:reason %)) (:quarantined index)))
    (is (every? #(string? (:message %)) (:quarantined index)))
    (is (= (:quarantined index) (:quarantined (reuse/index [free (bad 'a-bad) (bad 'z-bad)] context))))
    (is (= ['free] (mapv :name (reuse/candidates index '(forall [y Int] (= y (+ 0 y))) {}))))))

(deftest suggestions-use-only-lemmas-cited-by-the-checked-proof
  (let [r (spec/check 'writ.spec-demo.tree-spec
                      {:seed 1 :cache false :adequacy false :suggest true
                       :proof 'writ.spec-demo.tree-novary-proof})
        suggestion (:suggestion (first (filter #(= 'build-lists (:lemma %)) (:lemmas r))))]
    (is (= '(hint build-lists {:use [insert-keeps-bst to-list-insert] :induct xs :vary [acc]})
           (:hint suggestion)))
    (is (pos? (:reuse-candidates suggestion)))
    (is (integer? (get-in r [:reuse :indexed])))
    (is (pos? (get-in r [:reuse :lookups])))
    (is (pos? (get-in r [:reuse :candidates])))
    (is (vector? (get-in r [:reuse :quarantined])))))

(deftest quarantine-report-names-the-omitted-lemmas
  (let [message (#'writ.spec/format-report
                 {:ok true :spec 'demo-spec :target 'demo
                  :reuse {:indexed 1 :lookups 1 :candidates 0 :quarantined
                          [{:name 'bad-lemma :reason :normalization-failed :message "nested exists"}]}})]
    (is (str/includes? message "quarantined"))
    (is (str/includes? message "bad-lemma"))
    (is (str/includes? message "nested exists"))))

(deftest disabling-ranked-reuse-leaves-ordinary-hint-search-enabled
  (let [ranked {:name 'ranked :prop '(forall [x Int] (= (inc x) 1))}
        needed {:name 'needed :prop '(forall [x Int] (= (dec x) 0))}
        pools (atom [])
        attempt (fn [_ lemmas _ _]
                  (let [names (set (map :name lemmas))]
                    (swap! pools conj names)
                    {:proved (contains? names 'needed) :lemmas ['needed]}))
        result (#'writ.spec/suggest-proof
                {:law 'target :prop '(forall [x Int] (= (inc x) 1))}
                [ranked needed] attempt {} {} nil
                {:budget 1 :reuse false :reuse-context context})]
    (is (:hint result) (pr-str result))
    (is (seq @pools))
    (is (every? #(contains? % 'needed) @pools))
    (is (zero? (:reuse-candidates result 0)))))

(deftest a-failed-ranked-pool-does-not-consume-the-full-search-budget
  (let [ranked {:name 'ranked :prop '(forall [x Int] (= (inc x) 1))}
        needed {:name 'needed :prop '(forall [x Int] (= (dec x) 0))}
        calls (atom 0)
        attempt (fn [_ lemmas _ _]
                  (swap! calls inc)
                  {:proved (boolean (some #{'needed} (map :name lemmas)))
                   :lemmas ['needed]})
        result (#'writ.spec/suggest-proof
                {:law 'target :prop '(forall [x Int] (= (inc x) 1))}
                [ranked needed] attempt {} {} nil
                {:budget 1 :reuse-context context})]
    (is (:hint result) (pr-str result))
    (is (<= 2 @calls))
    (is (= ['needed] (-> result :hint (nth 2) :use)))))

(deftest an-overbroad-hint-use-is-replaced-by-actual-citations
  (let [ranked {:name 'ranked :prop '(forall [x Int] (= (inc x) 1))}
        needed {:name 'needed :prop '(forall [x Int] (= (dec x) 0))}
        attempt (fn [_ lemmas _ _]
                  {:proved (boolean (some #{'needed} (map :name lemmas)))
                   :lemmas ['needed]})
        result (#'writ.spec/suggest-proof
                {:law 'target :prop '(forall [x Int] (= (inc x) 1))}
                [ranked needed] attempt {} {} {:use ['ranked]}
                {:budget 1 :reuse-context context})]
    (is (= ['needed] (-> result :hint (nth 2) :use)))))
