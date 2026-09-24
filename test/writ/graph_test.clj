(ns writ.graph-test
  "Refinement types and the state graph.

  A refinement is a type and a predicate: its values are generated to
  satisfy the predicate, and the prover takes the predicate as a
  hypothesis.  A graph's nodes are types and its edges are fns: each edge
  is an obligation, checked and proved like a law, that the fn takes a
  value of its node to a value of one of the nodes it names.  With every
  edge proved, the graph's own rules hold for every run of the code."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.string :as str]
            [writ.spec :as spec]))

(defn- law-result [report nm]
  (first (filter #(= nm (:law %)) (:laws report))))

(defn- expansion-error [form]
  (try (macroexpand-1 form) nil
       (catch Throwable e (ex-message e))))

(deftest a-refinement-generates-only-its-values
  (let [tenv (spec/type-env 'writ.spec-demo.signal-spec)]
    (doseq [v (spec/sample 'Yellow tenv 200)]
      (is (spec/conforms? 'Yellow v tenv) (pr-str v)))
    (is (not (spec/conforms? 'Yellow [:Yellow 6] tenv)))
    (is (not (spec/conforms? 'Yellow [:Red 1] tenv)))
    (testing "an integer range is generated inside it, not filtered from wide samples"
      (let [tenv (spec/type-env 'writ.spec-demo.court-spec)]
        (is (every? #(<= 0 % 37) (spec/sample 'Row tenv 300)))
        (is (= #{0 37} (set (filter #{0 37} (spec/sample 'Row tenv 2000)))))))))

(deftest a-refinement-defines-its-predicate
  (require 'writ.spec-demo.signal-spec)
  (is (true? ((resolve 'writ.spec-demo.signal-spec/Green?) [:Green 3])))
  (is (false? ((resolve 'writ.spec-demo.signal-spec/Green?) [:Green 31]))))

(deftest a-refined-binder-is-a-hypothesis-to-the-prover
  (let [r (spec/check 'writ.spec-demo.court-spec {:seed 42})]
    (is (:ok r) (:message r))
    (is (= :proved (:status (law-result r 'idle-keeps-a-row-on-the-court))))))

(deftest every-edge-of-the-graph-is-proved
  (let [r (spec/check 'writ.spec-demo.signal-spec {:seed 42})]
    (is (:ok r) (:message r))
    (testing "one obligation per edge, named for the graph, the node and the fn"
      (doseq [nm '[signal:green:tick signal:yellow:tick signal:red:tick]]
        (is (= :proved (:status (law-result r nm))) (str nm ": " (pr-str (law-result r nm))))))
    (testing "a law over a refined type"
      (is (= :proved (:status (law-result r 'a-light-counts-up-while-it-shows)))))
    (is (= [{:graph 'signal :status :ok :states 3 :edges 3}] (:graphs r)))
    (is (str/includes? (:message r) "graph `signal`: 3 edges proved, each of their 6 steps taken"))))

(deftest every-step-of-the-graph-is-taken
  (let [r (spec/check 'writ.spec-demo.signal-spec {:seed 42})]
    (doseq [nm '[signal:green:tick->green signal:green:tick->yellow
                 signal:yellow:tick->yellow signal:yellow:tick->red
                 signal:red:tick->red signal:red:tick->green]]
      (is (= :witnessed (:status (law-result r nm))) (str nm ": " (pr-str (law-result r nm)))))
    (testing "the witness is the state, and any args, that takes the step"
      (is (= '{l [:Green 30]} (:witness (law-result r 'signal:green:tick->yellow)))))))

(deftest a-step-the-code-never-takes-fails
  (let [r (spec/check 'writ.spec-demo.signal-spec {:seed 42 :target 'writ.spec-demo.signal-stuck})]
    (is (not (:ok r)))
    (is (= :proved (:status (law-result r 'signal:green:tick))) "the light stays in its states...")
    (is (= :failed (:status (law-result r 'signal:green:tick->yellow))) "...but never turns yellow")
    (is (str/includes? (:message r) "law `signal:green:tick->yellow` fails"))
    (is (str/includes? (:message r)
                       "the graph says a tick can take green to yellow, but no generated green does"))))

(deftest code-that-leaves-the-graph-fails-its-edge
  (let [r (spec/check 'writ.spec-demo.signal-spec {:seed 42 :target 'writ.spec-demo.signal-skip})
        l (law-result r 'signal:yellow:tick)]
    (is (not (:ok r)))
    (is (= :failed (:status l)))
    (is (str/includes? (:message r) "law `signal:yellow:tick` fails for"))
    (is (str/includes? (:message r) "l = [:Yellow 5]"))
    (is (str/includes? (:message r) "a tick from yellow must land in yellow or red"))
    (is (not-any? :prover-bug (:laws r)))))

(deftest a-graph-that-breaks-its-own-rules-fails
  (let [r (spec/check 'writ.spec-demo.signal-draft-spec {:seed 42})]
    (is (not (:ok r)))
    (is (str/includes? (:message r) "graph `signal` breaks its own rules"))
    (is (str/includes? (:message r)
                       ":red must be reached only through :yellow, but :green -[tick]-> :red avoids it"))))

(deftest a-graph-must-fit-the-signatures
  (let [r (spec/check 'writ.spec-demo.signal-flow-spec {:seed 42})]
    (is (not (:ok r)))
    (is (str/includes? (:message r)
                       "graph `signal`: the edge :ticks -[tick]-> passes `tick` a Nat, but its ann takes (Tuple Keyword Nat)"))))

(deftest a-start-outside-its-node-fails
  (is (str/includes? (expansion-error '(writ.spec/graph g {:states {:a Nat} :edges {:a {[f] #{:b}}}}))
                     "`graph g`: the edge from :a names :b, which is not a state"))
  (is (str/includes? (expansion-error '(writ.spec/graph g {:states {:a Nat} :edges {} :start [:c 1]}))
                     "`graph g`: :start names :c, which is not a state"))
  (is (str/includes? (expansion-error '(writ.spec/graph g {:states {:a Nat} :edges {} :colour :red}))
                     "unknown keys"))
  (is (str/includes? (expansion-error '(writ.spec/refine Row [y] (pos? y)))
                     "(refine Name [x BaseType] predicate)")))

(deftest a-spec-must-declare-its-graph
  (let [r (spec/check 'writ.spec-demo.no-graph-spec {:seed 42})]
    (is (not (:ok r)))
    (is (str/includes? (:message r) "`writ.spec-demo.no-graph-spec` declares no state graph"))
    (is (str/includes? (:message r) "(graph name {:states {state Type ...} :edges {state {[fn ArgType ...] #{state ...}}}})"))))

(deftest a-refined-state-makes-its-edge-a-law
  (let [r (spec/check 'writ.spec-demo.flow-spec {:seed 42})]
    (is (:ok r) (:message r))
    (is (= [{:graph 'sorting :status :ok :states 2 :edges 1}] (:graphs r)))
    (is (= :witnessed (:status (law-result r 'sorting:unsorted:isort->sorted))))
    (is (contains? #{:proved :tested} (:status (law-result r 'sorting:unsorted:isort))))))

(deftest states-of-one-plain-type-cannot-be-told-apart
  (let [r (spec/check 'writ.spec-demo.flow-plain-spec {:seed 42})]
    (is (not (:ok r)))
    (is (str/includes? (:message r)
                       "graph `sorting`: :unsorted and :sorted are both (List Nat), so nothing tells them apart"))
    (is (str/includes? (:message r) "make each a refinement that says what sets it apart"))))

(deftest a-graph-step-is-proved-never-to-throw
  (let [r (spec/check 'writ.spec-demo.signal-spec {:seed 42})
        l (law-result r 'signal:yellow:tick)]
    (is (= :proved (:status l)))
    (is (true? (:total l)))
    (is (str/includes? (:proof l) "and it never throws"))))

(deftest a-step-that-throws-is-caught
  (let [r (spec/check 'writ.spec-demo.signal-spec {:seed 42 :target 'writ.spec-demo.signal-throw})
        l (law-result r 'signal:yellow:tick)]
    (is (not (:ok r)))
    (is (= :failed (:status l)) (pr-str l))
    (is (str/includes? (:message r) "l = [:Yellow 5]"))))

(deftest a-rare-refinement-is-still-generated
  (let [tenv (spec/type-env 'writ.spec-demo.signal-spec)]
    (is (every? #(= [:Red 30] %) (spec/sample 'Stopped tenv 1000)))))

(deftest an-edge-into-a-plain-state-beside-refined-ones-fails
  (let [r (spec/check 'writ.spec-demo.signal-mixed-spec {:seed 42})]
    (is (not (:ok r)))
    (is (some? (law-result r 'signal:green:tick)) "an edge into refinements only is still a law")
    (is (str/includes? (:message r)
                       "graph `signal`: the edge :yellow -[tick]-> lands in :red, a plain (Tuple Keyword Nat)"))
    (is (str/includes? (:message r) "make :red a refinement"))))

(deftest an-edge-can-take-its-state-at-any-parameter
  (let [r (spec/check 'writ.spec-demo.sort-spec {:seed 42})]
    (is (:ok r) (:message r))
    (testing "`_` marks the state: insert keeps a sorted list sorted"
      (is (contains? #{:proved :tested} (:status (law-result r 'sorting:sorted:insert)))))))

(deftest a-state-can-be-taken-out-of-a-result
  (let [r (spec/check 'writ.spec-demo.links-spec {:seed 42})]
    (is (:ok r) (:message r))
    (is (= [{:graph 'store :status :ok :states 2 :edges 2}] (:graphs r)))))

(deftest an-edge-marks-its-state-once
  (is (str/includes? (expansion-error '(writ.spec/graph g {:states {:a Nat} :edges {:a {[f _ _] #{:a}}}}))
                     "marks the state with `_` more than once"))
  (is (str/includes? (expansion-error '(writ.spec/graph g {:states {:a Nat} :edges {:a {[first Nat] #{:a}}}}))
                     "`first` takes the state alone")))

(deftest a-projection-must-fit-its-state
  (let [r (spec/check 'writ.spec-demo.links-bad-spec {:seed 42})]
    (is (not (:ok r)))
    (is (str/includes? (:message r)
                       "graph `store`: the edge :added -[second]-> :links expects a (Map String String), but `second` of :added gives a String"))))

(deftest a-graph-draws-as-a-state-diagram
  (let [m (spec/mermaid 'writ.spec-demo.signal-spec {:graph 'signal})]
    (is (str/starts-with? m "stateDiagram-v2"))
    (is (str/includes? m "[*] --> green"))
    (is (str/includes? m "green --> yellow : tick"))
    (is (str/includes? m "green : green, a Green"))))

(deftest the-plan-reads-from-the-spec-alone
  (let [p (spec/plan 'writ.spec-demo.pipeline-spec)]
    (is (str/includes? p "plan: writ.spec-demo.pipeline-spec for writ.spec-demo.pipeline"))
    (is (str/includes? p "graph `request`"))
    (is (str/includes? p ":clean     Clean, a String where (= s (cleaned s))"))
    (is (str/includes? p ":raw -[normalize]-> :clean"))
    (is (str/includes? p "handle  [String -> (Tuple Keyword String)]"))
    (is (str/includes? p "laws: handle-answers-with-the-cleaned-input, ok-exactly-when-short"))
    (is (str/includes? p "flow: s -> normalize -> respond -> result"))
    (is (str/includes? p "calls exactly: normalize, respond"))))

(deftest the-readmes-sort-spec-is-proved
  (let [r (spec/check 'writ.spec-demo.readme-sort-spec {:seed 42})]
    (is (:ok r) (:message r))
    (is (= :proved (:status (law-result r 'sorting:unsorted:isort))))
    (is (= :proved (:status (law-result r 'sorting:sorted:insert))))))
