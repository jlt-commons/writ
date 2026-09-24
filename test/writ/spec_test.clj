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
            [writ.types]
            [writ.lower]))

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
      (is (= :evaluated (:status (law-result r 'insert-empty))))
      (is (= :proved (:status (law-result r 'sorted))))
      (is (= :proved (:status (law-result r 'permutation))))
      (is (= :tested (:status (law-result r 'smallest-first))))
      (is (= :witnessed (:status (law-result r 'has-fixed-point)))))
    (testing "a tested law ran on generated inputs"
      (is (= 100 (:trials (law-result r 'sorted))))
      (is (integer? (:seed (law-result r 'sorted)))))
    (testing "a witness is shrunk to the simplest one"
      (is (= {'xs ()} (:witness (law-result r 'has-fixed-point)))))
    (testing "the spec pins down every fn it signs"
      (is (= [] (:gaps r))))))

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
    (is (= :proved (:status (law-result r 'size-counts))))
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

;; --- the spec must say what the code means --------------------------------

(deftest a-law-true-of-any-implementation-is-vacuous
  (let [r (spec/check 'writ.spec-demo.sort-vacuous-spec {:seed 42})
        st #(:status (law-result r %))]
    (is (not (:ok r)))
    (testing "a law writ.norm proves without the code"
      (is (= :vacuous (st 'sort-refl)))
      (is (re-find #"law `sort-refl` is vacuous: writ.norm proves it without looking at the implementation"
                   (:message r))))
    (testing "a law that never calls the code"
      (is (= :vacuous (st 'add-zero)))
      (is (= :vacuous (st 'count-self)))
      (is (re-find #"law `add-zero` is vacuous: it calls no fn of writ.spec-demo.sort"
                   (:message r))))
    (testing "a law about the code still runs"
      (is (= :tested (st 'sorted))))))

(deftest a-spec-that-does-not-pin-a-fn-down-has-gaps
  (let [r (spec/check 'writ.spec-demo.sort-weak-spec {:seed 42})
        gap-fns (set (map :fn (:gaps r)))]
    (is (every? #(contains? #{:tested :proved :witnessed} (:status %)) (:laws r)) "every law holds")
    (is (not (:ok r)) "but the spec is too weak to mean anything")
    (is (contains? gap-fns 'isort))
    (testing "the report names the impostor that satisfied every law"
      (is (re-find #"the spec does not pin down `isort`: every law still holds when it always returns"
                   (:message r))))))

(deftest adequacy-can-be-skipped
  (is (:ok (spec/check 'writ.spec-demo.sort-weak-spec {:seed 42 :adequacy false}))))

(deftest impostors-are-well-typed
  (let [ms (spec/impostors 'isort {:params '[(List Nat)] :ret '(List Nat)} '[xs] {} 42)]
    (is (some #(= "returns its argument `xs` unchanged" (:desc %)) ms))
    (is (some #(re-find #"^always returns" (:desc %)) ms))
    (is (some #(re-find #"reversed" (:desc %)) ms))
    (doseq [m ms]
      (is (spec/conforms? '(List Nat) (((:make m) (fn [xs] (sort xs))) [3 1 2]) {})
          (:desc m)))))

(deftest the-tree-spec-pins-down-its-fns
  (let [r (spec/check tree-spec {:seed 42})]
    (is (:ok r) (:message r))
    (is (= [] (:gaps r)))
    (is (= :proved (:status (law-result r 'holds-a-sorted-set))))))

;; --- adequacy for keyword results and pinned arguments ---------------------

(def ^:private classify-spec 'writ.spec-demo.classify-spec)

(deftest a-keyword-result-is-perturbed
  (let [ms (spec/impostors 'classify-read {:params '[Int Bool] :ret 'Keyword} '[n e] {} 42)
        real (fn [n _] (if (pos? n) :data :idle))]
    (is (some #(= :perturbed (:kind %)) ms))
    (doseq [m ms :when (= :perturbed (:kind m))]
      (let [imp ((:make m) real)]
        (is (keyword? (imp 5 true)) (:desc m))
        (is (not= (real 5 true) (imp 5 true)) (:desc m))))))

(deftest a-classifier-spec-pins-down-its-fn
  (let [r (spec/check classify-spec {:seed 42})]
    (is (:ok r) (:message r))
    (is (= [] (:gaps r)))
    (testing "a passing report says what the spec rejected"
      (is (some #(= :perturbed (:kind %)) (:rejected (first (:rejected r)))))
      (is (re-find #"`classify-read`: 5 laws, \d+ impostors rejected \(\d+ constant, \d+ perturbed\)"
                   (:message r))))))

(deftest laws-that-fix-an-argument-leave-the-rest-unspecified
  (let [r (spec/check 'writ.spec-demo.classify-weak-spec {:seed 42})]
    (is (every? #(contains? #{:tested :proved :witnessed} (:status %)) (:laws r)) "every law holds")
    (is (not (:ok r)))
    (is (= ['classify-read] (map :fn (:gaps r))))
    (is (re-find #"when it returns a different value whenever `n` is not one of -127, -2, -1, 0"
                 (:message r)))))

(deftest an-argument-fixed-to-every-value-of-its-type-is-covered
  (let [ms (spec/impostors 'f {:params '[Int Bool] :ret 'Keyword} '[n e] {} 42
                           {0 #{0 1} 1 #{true false}})]
    (is (= ["returns a different value whenever `n` is not one of 0, 1"]
           (map :desc (filter #(= :off-pin (:kind %)) ms))))))

;; --- scan: which fns a spec could cover ------------------------------------

(deftest scan-sorts-a-namespace-by-what-writ-can-check
  (let [{:keys [forms message]} (spec/scan 'writ.spec-demo.scan-mixed)
        st (into {} (map (juxt :name :status)) forms)
        why (into {} (map (juxt :name :why)) forms)]
    (is (= '{classify :ok, shout :no, log! :no, loud-classify :no, Conn :no, total :needs-ann}
           st))
    (testing "each rejection carries writ's own reason"
      (is (re-find #"`\.toUpperCase` is host interop" (why 'shout)))
      (is (re-find #"`println` in `log!` is effect code" (why 'log!)))
      (is (re-find #"`defrecord` is not supported" (why 'Conn)))
      (testing "in the words of the spec workflow, not writ.defn's books"
        (is (not (re-find #"book|law and proof" (why 'Conn))))
        (is (re-find #"def and defn" (why 'Conn)))))
    (testing "a fn that calls a rejected one says which"
      (is (= "it uses `shout`, which writ cannot check" (why 'loud-classify))))
    (testing "an unsigned collection is a missing ann, not a rejection"
      (is (re-find #"must be a finite collection" (why 'total))))
    (testing "the summary groups them"
      (is (str/starts-with? message "writ.spec/scan writ.spec-demo.scan-mixed: 1 of 6 forms can be checked, 1 more once signed"))
      (is (str/includes? message "\n  shout (private): "))
      (is (str/includes? message "\n  Conn (defrecord): ")))))

(deftest scan-reads-a-namespace-without-its-spec
  (testing "pure code that needs no types passes as it is"
    (is (every? #(= :ok (:status %)) (:forms (spec/scan 'writ.spec-demo.tree)))))
  (testing "a sort over an unsigned list is checkable once signed"
    (let [st (into {} (map (juxt :name :status)) (:forms (spec/scan 'writ.spec-demo.sort)))]
      (is (= '{insert :needs-ann, isort :needs-ann} st)))
    (is (= "it uses `insert`, which needs an `ann` first"
           (:why (second (:forms (spec/scan 'writ.spec-demo.sort))))))))

(deftest scan-rejects-static-host-members-and-accepts-doseq
  (let [{:keys [forms]} (spec/scan 'writ.spec-demo.scan-host)
        st (into {} (map (juxt :name :status)) forms)
        why (into {} (map (juxt :name :why)) forms)]
    (testing "System/getenv and System/currentTimeMillis are host interop"
      (is (= :no (st 'env)))
      (is (re-find #"`System/getenv` is host interop" (str (why 'env))))
      (is (= :no (st 'now))))
    (testing "a doseq is a loop that is not the fn's last form"
      (is (not (re-find #"tail position" (str (why 'touch-all)))))
      (testing "and it is missing a type, named in the code's own words"
        (is (= :needs-ann (st 'touch-all)))
        (is (re-find #"a macro's loop in `touch-all`, such as a `doseq`" (why 'touch-all)))
        (is (re-find #"`xs` must be a finite collection" (why 'touch-all)))
        (is (not (re-find #"G__" (why 'touch-all))))))
    (testing "a loop's recur that keeps an accumulator first names the fix"
      (is (re-find #"`recur` in `loop-sum` does not descend" (str (why 'loop-sum))))
      (is (re-find #"put `ys` first in the `loop` bindings" (str (why 'loop-sum)))))))

(deftest pinned-args-ignore-calls-that-leave-an-argument-out
  (is (= {0 #{1}} (#'spec/pinned-args '[(f 1 2) (f 1)] 'f 2))))

;; --- calls: the call graph the spec pins -------------------------------------

(def ^:private pipeline-spec 'writ.spec-demo.pipeline-spec)

(defn- calls-run [target]
  (spec/check pipeline-spec {:target target :seed 42 :adequacy false :prove false}))

(deftest a-target-that-keeps-its-layers-meets-its-calls
  (let [r (calls-run nil)]
    (is (:ok r) (:message r))
    (is (= '[{:fn handle :calls [normalize respond] :status :ok}
             {:fn normalize :calls [clojure.string/lower-case clojure.string/trim] :status :ok}
             {:fn respond :calls [valid?] :status :ok}
             {:fn valid? :calls [] :status :ok}]
           (:calls r)))
    (is (str/includes? (:message r) "`handle` calls exactly normalize, respond"))))

(deftest inlining-a-helper-breaks-the-call-graph
  (let [r (calls-run 'writ.spec-demo.pipeline-inline)
        c (first (filter #(= 'handle (:fn %)) (:calls r)))]
    (is (not (:ok r)))
    (testing "the laws still hold: only the call graph catches it"
      (is (every? #(not= :failed (:status %)) (:laws r))))
    (is (= :failed (:status c)))
    (is (= '[normalize] (:missing c)))
    (is (= '[clojure.string/lower-case clojure.string/trim] (:extra c)))
    (is (str/includes? (:message r) "`handle` does not call `normalize`, which the spec says it calls"))
    (is (str/includes? (:message r) "`handle` calls `clojure.string/lower-case`, which the spec does not list"))))

(deftest skipping-a-layer-breaks-the-call-graph
  (let [c (first (filter #(= 'handle (:fn %))
                         (:calls (calls-run 'writ.spec-demo.pipeline-bypass))))]
    (is (= '[respond] (:missing c)))
    (is (= '[valid?] (:extra c)))))

(deftest a-local-that-shadows-a-fn-is-not-a-call-to-it
  (let [c (first (filter #(= 'handle (:fn %))
                         (:calls (calls-run 'writ.spec-demo.pipeline-shadow))))]
    (is (= '[respond] (:missing c)))
    (is (= '[valid?] (:extra c)))))

(deftest calls-must-name-the-target-s-fns
  (let [r (spec/check 'writ.spec-demo.pipeline-unknown-spec {:seed 42 :adequacy false :prove false})]
    (is (not (:ok r)))
    (is (str/includes? (:message r) "the spec says `handle` calls `normalise`, but writ.spec-demo.pipeline defines no fn `normalise`"))
    (is (str/includes? (:message r) "the spec gives `render` a call set, but writ.spec-demo.pipeline defines no fn `render`"))))

(deftest call-graph-reads-any-namespace
  (is (= '{normalize #{clojure.string/lower-case clojure.string/trim}
           valid? #{}
           respond #{valid?}
           handle #{normalize respond}}
         (spec/call-graph 'writ.spec-demo.pipeline)))
  (testing "effect code too: it is read, not checked"
    (let [g (spec/call-graph 'writ.spec-demo.scan-mixed)]
      (is (= '#{shout classify} (get g 'loud-classify)))
      (is (= #{} (get g 'log!))))))

(deftest mermaid-draws-the-call-graph
  (let [m (spec/mermaid 'writ.spec-demo.pipeline)]
    (is (str/starts-with? m "flowchart LR"))
    (is (str/includes? m "handle --> normalize"))
    (is (str/includes? m "handle --> respond"))
    (is (str/includes? m "normalize --> clojure_string_lower_case")))
  (testing "given a spec, it draws the target and marks calls the spec does not list"
    (let [m (spec/mermaid pipeline-spec {:target 'writ.spec-demo.pipeline-bypass})]
      (is (str/includes? m "handle -.->|not in spec| valid_Q"))
      (is (str/includes? m "handle --x|missing| respond")))))

(deftest a-local-fn-s-unknown-return-does-not-fail-a-signed-return
  ;; inference types a local fn's return it cannot work out as Any; that is
  ;; an unknown, so the signed return type still holds
  (is (writ.types/compat? '(Tuple Keyword String) 'Any {}))
  (is (:ok (:static (calls-run 'writ.spec-demo.pipeline-shadow)))))

(deftest a-false-or-nil-case-default-is-a-default
  (doseq [d [false nil]]
    (is (= {:op :lit :val d}
           (:default (writ.lower/lower (list 'case '(first t) :Leaf true d))))))
  (is (nil? (:default (writ.lower/lower '(case (first t) :Leaf true :Node false))))))

(deftest a-case-on-a-field-of-a-tuple-must-cover-every-constructor
  (let [r (spec/check 'writ.spec-demo.light-spec {:seed 42})]
    (is (not (:ok (:static r))))
    (is (str/includes? (:message r) "the `case` on `light` (Light) does not handle :Amber"))))

(deftest a-failing-let-is-reported-whole
  (let [r (spec/check 'writ.spec-demo.sort-let-spec
                      {:target 'writ.spec-demo.sort-desc :seed 42 :adequacy false :prove false})
        d (:detail (law-result r 'smallest-first))]
    (is (not (:ok r)))
    (is (= 1 (count d)) (pr-str d))
    (is (not (str/includes? (:message r) "Unable to resolve")))))

(deftest a-helper-the-prover-cannot-read-leaves-laws-tested
  (let [r (spec/check 'writ.spec-demo.sort-pairs-spec {:seed 42 :adequacy false})]
    (is (= :tested (:status (law-result r 'sorted))) (:message r))))

(deftest a-fn-literal-may-destructure-its-parameters
  (is (= :fn (:op (writ.lower/lower '(fn [[a b] {:keys [c]} & [d]] (+ a b c d))))))
  (testing "defn params too, through the spec's static check"
    (let [r (spec/check 'writ.spec-demo.sort-pairs-spec
                        {:target 'writ.spec-demo.sort-pairs :seed 42 :adequacy false})]
      (is (:ok (:static r)) (:message r))
      (is (:ok r) (:message r)))))

(deftest a-fn-literal-argument-is-not-shown-as-a-value
  (let [r (spec/check 'writ.spec-demo.sort-every-spec
                      {:target 'writ.spec-demo.sort-desc :seed 42 :adequacy false :prove false})
        d (:detail (law-result r 'every-prefix-starts-low))]
    (is (not (:ok r)))
    (is (not-any? #(str/includes? (second %) "#object") d) (pr-str d))))

(deftest recursion-down-a-nat-by-more-than-one
  (let [r (spec/check 'writ.spec-demo.nat-chain-spec {:seed 42 :adequacy false :prove false})]
    (is (:ok r) (:message r)))
  (testing "a guard that proves too little is not enough"
    (let [r (spec/check 'writ.spec-demo.nat-chain-spec
                        {:target 'writ.spec-demo.nat-chain-short :seed 42 :adequacy false})]
      (is (not (:ok (:static r))))
      (is (re-find #"thirds" (:message r)) (:message r)))))

;; --- machine: a step fn against its transition table --------------------------

(deftest a-step-that-follows-its-table-meets-its-machine
  (let [r (spec/check 'writ.spec-demo.turnstile-spec {:seed 42})]
    (is (:ok r) (:message r))
    (is (= '[{:machine turnstile :status :ok :states 3 :events 4}] (:machines r)))
    (is (str/includes? (:message r) "machine `turnstile`: 12 transitions checked"))))

(deftest a-step-off-its-table-is-caught
  (let [r (spec/check 'writ.spec-demo.turnstile-spec
                      {:target 'writ.spec-demo.turnstile-free-ride :seed 42})
        m (first (:machines r))]
    (is (not (:ok r)))
    (is (= :failed (:status m)))
    (is (= '[{:state [:Broken] :event [:Coin] :expected [:Broken] :actual [:Unlocked]}]
           (:mismatches m)))
    (is (str/includes? (:message r)
                       "(step [:Broken] [:Coin]) is [:Unlocked], but the table says [:Broken] (no transition listed: the state stays)"))))

(deftest the-table-is-checked-against-its-own-constraints
  (let [r (spec/check 'writ.spec-demo.turnstile-graph-spec {:seed 42})
        m (first (:machines r))]
    (is (not (:ok r)))
    (is (= [] (:mismatches m)) "the code follows the table...")
    (is (str/includes? (:message r) "from [:Broken] no final state can be reached")
        "...but the table traps a broken turnstile")
    (is (str/includes? (:message r)
                       "[:Unlocked] must never lead to [:Broken], but it does: [:Unlocked] -[:Kick]-> [:Broken]"))
    (is (str/includes? (:message r)
                       "[:Broken] must be reached only through [:Unlocked], but [:Locked] -[:Kick]-> [:Broken] avoids it"))))

(deftest a-machine-draws-as-a-state-diagram
  (let [m (spec/mermaid 'writ.spec-demo.turnstile-spec {:machine 'turnstile})]
    (is (str/starts-with? m "stateDiagram-v2"))
    (is (str/includes? m "[*] --> Locked"))
    (is (str/includes? m "Locked --> Unlocked : Coin"))
    (is (str/includes? m "Locked --> [*]"))))

;; --- a law judges the code with the spec's own helpers ------------------------

(deftest a-helper-named-like-a-target-fn-is-rejected
  (let [r (spec/check 'writ.spec-demo.shadow-spec {:seed 42})]
    (is (not (:ok r)))
    (is (= '[ascending?] (:ambiguous r)))
    (is (empty? (:laws r)) "no law runs while a name means two things")
    (is (str/includes? (:message r)
                       "`ascending?` is defined by the spec and by writ.spec-demo.shadow"))
    (is (str/includes? (:message r) "rename the spec's `ascending?`"))))

;; --- the spec bounds the code's public fns --------------------------------------

(deftest a-public-fn-the-spec-does-not-sign-fails
  (let [r (spec/check spec-ns {:target 'writ.spec-demo.sort-extra :seed 42})]
    (is (not (:ok r)))
    (is (= '[largest] (:unspecified r)))
    (is (str/includes? (:message r)
                       "`largest` is public, but the spec gives it no signature"))
    (is (str/includes? (:message r) "make it private with defn-"))))

(deftest the-report-names-public-fns-off-the-graph
  (let [r (spec/check spec-ns {:seed 42})]
    (is (:ok r) (:message r))
    (is (= [] (:off-graph r)) "insert is a step: it keeps a sorted list sorted"))
  (let [r (spec/check 'writ.spec-demo.flow-spec {:seed 42})]
    (is (= '[insert] (:off-graph r)))
    (is (str/includes? (:message r) "not a step of any graph or machine: insert"))))
