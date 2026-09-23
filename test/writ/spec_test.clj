(ns writ.spec-test
  "writ.spec: a spec namespace constrains plain Clojure it never touches.

  One spec (writ.spec-demo.sort-spec) is checked against a correct insertion
  sort and against broken ones.  Each broken one must be rejected, and the
  report must say what to fix: the law, the smallest input that breaks it,
  and the values each side produced."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.string :as str]
            [writ.core :as wc]
            [writ.spec :as spec]
            [writ.book]
            [writ.types]))

(def ^:private spec-ns 'writ.spec-demo.sort-spec)

(defn- run [target]
  (spec/check spec-ns {:target target :seed 42}))

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
      (is (= 100 (:trials (law-result r 'sorted))))
      (is (integer? (:seed (law-result r 'sorted)))))
    (testing "a witness is shrunk to the simplest one"
      (is (= {'xs ()} (:witness (law-result r 'has-fixed-point)))))))

(deftest trials-is-the-number-of-tests
  (let [r (spec/check spec-ns {:trials 300})]
    (is (= 300 (:trials (law-result r 'permutation))))))

(deftest every-type-has-a-generator-whose-values-conform
  (let [tenv {'Tree {:arity 0 :params [] :ctors {'Leaf {:fields []}
                                                 'Node {:fields ['Tree 'Nat 'Tree]}}}
              'Box {:arity 1 :params ['a] :ctors {'Wrap {:fields ['a]}}}}]
    (doseq [t '[Nat Int Bool Char String Keyword Symbol Double Unit Any
                (List Nat) (Vec Int) (Set Keyword) (Map Keyword Nat)
                (Tuple Nat String) Tree (Box (List Bool))]]
      (testing (pr-str t)
        (is (every? #(spec/conforms? t % tenv)
                    (spec/sample t tenv 50)))))
    (testing "recursive data stays finite and reaches its recursive case"
      (is (some vector? (spec/sample 'Tree tenv 50))))))

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
    (testing "the counterexample is shrunk to two copies of x"
      (let [{x 'x xs 'xs} (:counterexample l)]
        (is (= 2 (count xs)))
        (is (every? #(= x %) xs))))
    (testing "the message names the law, the input, both sides and the seed"
      (let [m (:message r)]
        (is (str/includes? m "law `permutation` fails"))
        (is (re-find #"xs = [\[(](\d+) \1[\])]" m))
        (is (str/includes? m "(occurrences x (isort xs)) => 1"))
        (is (str/includes? m "(occurrences x xs) => 2"))
        (is (str/includes? m ":seed 42"))))))

(deftest a-seed-replays-the-same-failure
  (let [a (law-result (run 'writ.spec-demo.sort-dedup) 'permutation)
        b (law-result (run 'writ.spec-demo.sort-dedup) 'permutation)]
    (is (= 42 (:seed a)))
    (is (= (:counterexample a) (:counterexample b)))
    (is (= (:original a) (:original b)))))

(deftest a-random-seed-is-reported
  (let [l (law-result (spec/check spec-ns {:target 'writ.spec-demo.sort-desc}) 'sorted)]
    (is (= :failed (:status l)))
    (is (integer? (:seed l)))
    (is (= 2 (count (get (:counterexample l) 'xs))))))

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

;; --- (List T) is any seq, not only a list ----------------------------------

(deftest list-types-generate-every-kind-of-seq
  (let [xs (spec/sample '(List Nat) {} 200)]
    (is (some list? xs))
    (is (some vector? xs))
    (is (some #(and (seq? %) (not (list? %))) xs))
    (is (some nil? xs))))

(deftest code-that-assumes-a-list-is-caught
  ;; conj prepends to a list but appends to a vector
  (let [r (run 'writ.spec-demo.sort-conj)
        l (law-result r 'insert-keeps-sorted)]
    (is (:ok (:static r)))
    (is (= :failed (:status l)))
    (is (vector? (get (:counterexample l) 'xs)))
    (is (= :tested (:status (law-result r 'sorted)))
        "isort only ever hands insert its own lists")))

;; --- data types, taken apart in plain Clojure -----------------------------

(def ^:private tree-spec 'writ.spec-demo.tree-spec)

(defn- tree-run [target]
  (spec/check tree-spec {:target target :seed 42}))

(deftest a-tree-taken-apart-with-case-meets-its-spec
  (let [r (spec/check tree-spec {:seed 42})]
    (is (:ok r) (:message r))
    (is (= :tested (:status (law-result r 'size-counts))))
    (is (= :tested (:status (law-result r 'insert-keeps-order))))
    (is (= :evaluated (:status (law-result r 'insert-into-empty))))))

(deftest a-case-on-the-tag-must-cover-every-constructor
  (let [r (tree-run 'writ.spec-demo.tree-missing-case)]
    (is (not (:ok r)))
    (is (re-find #"`size`.*does not handle :Leaf" (get-in r [:static :error])))))

(deftest a-case-clause-must-name-a-constructor
  (let [r (tree-run 'writ.spec-demo.tree-typo)]
    (is (not (:ok r)))
    (is (re-find #":Nod is not a constructor of Tree" (get-in r [:static :error])))))

(deftest a-built-value-has-its-constructor-s-fields
  (let [r (tree-run 'writ.spec-demo.tree-bad-build)]
    (is (not (:ok r)))
    (is (re-find #"Node takes 3 field\(s\) but is built with 2" (get-in r [:static :error])))))

(deftest destructuring-stops-at-the-constructor-s-fields
  (let [r (tree-run 'writ.spec-demo.tree-overread)]
    (is (not (:ok r)))
    (is (re-find #"Node has 3 field\(s\)" (get-in r [:static :error])))))

(deftest a-wrong-tree-insert-fails-with-a-tree-counterexample
  (let [r (tree-run 'writ.spec-demo.tree-mirror)
        l (law-result r 'insert-keeps-order)]
    (is (:ok (:static r)))
    (is (= :failed (:status l)))
    (is (spec/conforms? 'Tree (get (:counterexample l) 't)
                        {'Tree {:arity 0 :params [] :ctors {'Leaf {:fields []}
                                                           'Node {:fields '[Tree Nat Tree]}}}}))
    (is (re-find #"\(to-list \(insert x t\)\) =>" (:message r)))))

(deftest outside-a-case-the-tag-is-not-read
  (let [err (fn [src]
              (try (writ.book/check-book src) nil
                   (catch Throwable e (ex-message e))))]
    (binding [writ.types/*tagged* true]
      (is (re-find #"take it apart with `\(case \(first t\) \.\.\.\)`"
                   (err '[(data Tree Leaf (Node Tree Nat Tree))
                          (defn f [^{:writ/type Tree} t] (second t))]))))))

;; --- built values: field types checked at compile time -----------------------

(defn- tagged-err [forms]
  (binding [writ.types/*tagged* true]
    (try (writ.book/check-book forms) nil
         (catch Throwable e (ex-message e)))))

(deftest a-provably-wrong-field-is-caught-before-running
  (let [r (tree-run 'writ.spec-demo.tree-bad-field)]
    (is (not (:ok r)))
    (is (re-find #"`insert`: field 1 of Node expects Tree but is given Nat"
                 (get-in r [:static :error])))
    (is (empty? (:laws r)))))

(deftest field-types-are-checked-only-when-known
  (testing "a built value may nest other built values"
    (is (nil? (tagged-err '[(data Tree Leaf (Node Tree Nat Tree))
                            (defn one [^{:writ/type Nat} x] [:Node [:Leaf] x [:Leaf]])]))))
  (testing "an unknown value passes: only a provable mismatch is an error"
    (is (nil? (tagged-err '[(data Tree Leaf (Node Tree Nat Tree))
                            (defn one [x] [:Node [:Leaf] x [:Leaf]])]))))
  (testing "a built subtree in a Nat field is rejected"
    (is (re-find #"field 2 of Node expects Nat but is given Tree"
                 (tagged-err '[(data Tree Leaf (Node Tree Nat Tree))
                               (defn bad [] [:Node [:Leaf] [:Leaf] [:Leaf]])])))))

(deftest parametric-fields-are-instantiated-from-their-values
  (testing "consistent instantiation passes and types the value"
    (is (nil? (tagged-err '[(data Pair [a] (MkPair a a))
                            (defn p [] [:MkPair 1 2])])))
    (is (re-find #"`q` returns \(Box String\) but its body has type \(Box Nat\)"
                 (tagged-err '[(data Box [a] (Wrap a))
                               (defn ^{:tag (Box String)} q [] [:Wrap 1])])))
    (is (nil? (tagged-err '[(data Box [a] (Wrap a))
                            (defn ^{:tag (Box Nat)} q [] [:Wrap 1])]))))
  (testing "a parameter given two different types is rejected"
    (is (re-find #"`p`: field 2 of MkPair expects a, which field 1 made Nat, but is given String"
                 (tagged-err '[(data Pair [a] (MkPair a a))
                               (defn p [] [:MkPair 1 "x"])])))))
