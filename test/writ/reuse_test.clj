(ns writ.reuse-test
  (:require [clojure.test :refer [deftest is testing]]
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

(deftest suggestions-use-only-lemmas-cited-by-the-checked-proof
  (let [r (spec/check 'writ.spec-demo.tree-spec
                      {:seed 1 :cache false :adequacy false :suggest true
                       :proof 'writ.spec-demo.tree-novary-proof})
        suggestion (:suggestion (first (filter #(= 'build-lists (:lemma %)) (:lemmas r))))]
    (is (= '(hint build-lists {:use [insert-keeps-bst to-list-insert] :induct xs :vary [acc]})
           (:hint suggestion)))))

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
