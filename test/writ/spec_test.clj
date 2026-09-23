(ns writ.spec-test
  "writ.spec: a spec namespace constrains plain Clojure it never touches.

  One spec (writ.spec-demo.sort-spec) is checked against a correct insertion
  sort and against broken ones.  Each broken one must be rejected, and the
  report must say what to fix: the law, the smallest input that breaks it,
  and the values each side produced."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.string :as str]
            [writ.core :as wc]
            [writ.spec :as spec]))

(def ^:private spec-ns 'writ.spec-demo.sort-spec)

(defn- run [target]
  (spec/check spec-ns {:target target}))

(defn- law-result [report nm]
  (first (filter #(= nm (:law %)) (:laws report))))

;; --- the correct implementation -----------------------------------------

(deftest correct-sort-meets-its-spec
  (let [r (spec/check spec-ns)]
    (is (:ok r) (:message r))
    (is (= 'writ.spec-demo.sort (:target r)))
    (testing "each law says how it was discharged"
      (is (= :proved (:status (law-result r 'add-zero))))
      (is (= :evaluated (:status (law-result r 'insert-empty))))
      (is (= :tested (:status (law-result r 'sorted))))
      (is (= :tested (:status (law-result r 'permutation))))
      (is (= :tested (:status (law-result r 'smallest-first))))
      (is (= :witnessed (:status (law-result r 'has-fixed-point)))))
    (testing "a tested law ran on generated inputs"
      (is (<= 100 (:trials (law-result r 'sorted)))))))

(deftest check!-returns-the-report-or-throws
  (is (:ok (spec/check! spec-ns)))
  (is (thrown-with-msg? Exception #"law `sorted`"
        (spec/check! spec-ns {:target 'writ.spec-demo.sort-desc}))))

;; --- wrong behaviour: laws catch it, with a shrunk counterexample -------

(deftest dropping-duplicates-breaks-permutation
  (let [r (run 'writ.spec-demo.sort-dedup)
        l (law-result r 'permutation)]
    (is (not (:ok r)))
    (is (= :failed (:status l)))
    (testing "the counterexample is shrunk to the smallest failing input"
      (is (= {'x 0 'xs '(0 0)} (:counterexample l))))
    (testing "the message names the law, the input and both sides"
      (let [m (:message r)]
        (is (str/includes? m "law `permutation` fails"))
        (is (str/includes? m "xs = (0 0)"))
        (is (str/includes? m "(occurrences x (isort xs)) => 1"))
        (is (str/includes? m "(occurrences x xs) => 2"))))))

(deftest flipped-comparison-breaks-sorted
  (let [r (run 'writ.spec-demo.sort-desc)
        l (law-result r 'sorted)]
    (is (not (:ok r)))
    (is (= :failed (:status l)))
    (is (= 2 (count (get (:counterexample l) 'xs))))
    (testing "a predicate law shows the values its arguments took"
      (is (re-find #"\(isort xs\) => \(1 0\)" (:message r))))))

(deftest a-total-well-typed-no-op-is-still-rejected
  (let [r (run 'writ.spec-demo.sort-identity)]
    (is (not (:ok r)))
    (is (:ok (:static r)) "it passes every static rule")
    (is (= :failed (:status (law-result r 'sorted))))
    (testing "laws its insert happens to satisfy still hold"
      (is (= :evaluated (:status (law-result r 'insert-empty)))))))

(deftest the-old-law-gate-cannot-tell
  ;; for contrast: the book-style laws the examples used are true of any
  ;; implementation, so a constant sort passed them
  (is (= {:ok true}
         (wc/check-book
           '[(writ.defn/defn sort [xs :- (List Nat)] :- Nat 42)
             (writ.defn/law sort-refl (= (sort xs) (sort xs)))
             (writ.defn/proof sort-refl-p sort-refl refl)]))))

;; --- static rules still apply to the unannotated source ------------------

(deftest static-rules-run-on-plain-source
  (testing "the ann'd return type is checked against the body"
    (let [r (run 'writ.spec-demo.sort-count)]
      (is (not (:ok r)))
      (is (re-find #"isort" (get-in r [:static :error])))
      (is (empty? (:laws r)) "laws do not run on code that failed statically")))
  (testing "recursion must descend, no marker needed"
    (let [r (run 'writ.spec-demo.sort-loop)]
      (is (not (:ok r)))
      (is (re-find #"does not descend" (get-in r [:static :error])))))
  (testing "effects are rejected"
    (let [r (run 'writ.spec-demo.sort-effect)]
      (is (not (:ok r)))
      (is (re-find #"println" (get-in r [:static :error]))))))

(deftest spec-names-must-exist-in-the-target
  (let [r (run 'writ.spec-demo.sort-missing)]
    (is (not (:ok r)))
    (is (re-find #"`insert`" (:message r)))))

;; --- instrument: runtime checks from the same signatures ---------------

(deftest instrument-checks-args-and-returns
  (let [insert (fn [& args] (apply @(resolve 'writ.spec-demo.sort/insert) args))]
    (spec/instrument spec-ns)
    (try
      (is (= '(1 2) (insert 1 '(2))))
      (is (thrown-with-msg? Exception #"`insert` argument 1 \(x\) expects Nat"
            (insert "a" '(2))))
      (finally (spec/unstrument spec-ns)))
    (testing "unstrument restores the original fns"
      (is (= '("a") (insert "a" ()))))))

(deftest check-leaves-a-callers-instrument-in-place
  (let [insert (fn [& args] (apply @(resolve 'writ.spec-demo.sort/insert) args))]
    (spec/instrument spec-ns)
    (try
      (is (:ok (spec/check spec-ns)))
      (is (thrown-with-msg? Exception #"expects Nat" (insert "a" ())))
      (finally (spec/unstrument spec-ns)))))
