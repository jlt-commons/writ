(ns writ.shell-test
  "A pure core split over namespaces, checked through the effect shell that
  uses it: the call graph reads multi-arity fns, macros and alias-qualified
  keywords; the prover follows calls into the core's other namespaces and
  reasons about values of type Any; generators reach the literals the code
  branches on; a graph edge can pass the spec's own fn, and be let off proof
  with a reason."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.string :as str]
            [writ.spec :as spec]))

(defn- law-result [report nm]
  (first (filter #(= nm (:law %)) (:laws report))))

(deftest the-call-graph-reads-every-arity-and-macros
  (let [g (spec/call-graph 'writ.spec-demo.verdict-shell)]
    (is (= '#{writ.spec-demo.verdict/restart?} (get g 'decide)))
    (is (= '#{decide} (get g 'decide-all)))
    (is (contains? (get g 'when-restart) 'writ.spec-demo.verdict/restart?))))

(deftest the-spec-holds-and-its-laws-are-proved
  (let [r (spec/check 'writ.spec-demo.verdict-spec {:seed 7})]
    (is (:ok r) (:message r))
    (testing "an Any law, through a call into another namespace"
      (is (= :proved (:status (law-result r 'permanent-always-restarts))))
      (is (= :proved (:status (law-result r 'temporary-never-restarts)))))
    (testing "vector? is decided for literals, lists and scalars"
      (doseq [l '[payload-of-an-ok-vector a-list-is-not-a-vector anything-else-is-bad]]
        (is (= :proved (:status (law-result r l))) (str l))))
    (testing "the code's literals seed the generator"
      (is (= :witnessed (:status (law-result r 'some-exit-is-orderly)))))
    (testing "a graph edge passed the spec's fn is proved, and its stale marker reported"
      (is (= :proved (:status (law-result r 'keeping:all:keep-if))))
      (is (str/includes? (:message r) "`keeping:all:keep-if` is marked {:require :tested}, but it is now proved")))
    (testing "the report tells proofs for every input from closed examples"
      (is (pos? (:general (:proof r))))
      (is (re-find #"\(\d+ for every input, \d+ on particular values\)" (:message r)) (:message r)))
    (testing "qualified names of the shell's own fns, a macro, and a reach into the core's own helpers, are wired"
      (is (every? #(= :ok (:status %)) (:calls r)) (pr-str (:calls r))))))

(deftest a-graph-tested-reason-must-be-given
  (is (thrown? Throwable
               (macroexpand-1 '(writ.spec/graph g {:states {:a Nat} :edges {:a {[inc] #{:a}}}
                                                   :tested {:a ""}})))))
