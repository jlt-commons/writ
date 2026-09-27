(ns writ.flow-test
  "`flow`: how data moves through a fn.  Each chain says a value reaches a
  step: a parameter, or what a step returns, is passed (maybe through
  other calls) to the next step, and the last may be the fn's result.
  The check reads the fn's source, so code that calls every layer the
  spec names but wires them wrong is caught."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.string :as str]
            [writ.spec :as spec]))

(defn- expansion-error [form]
  (try (macroexpand-1 form) nil
       (catch Throwable e (ex-message e))))

(defn- flow-of [r f] (first (filter #(= f (:fn %)) (:flows r))))

(deftest a-fn-wired-as-planned-passes
  (let [r (spec/check 'writ.spec-demo.pipeline-spec {:seed 42})]
    (is (:ok r) (:message r))
    (is (= :ok (:status (flow-of r 'handle))))
    (is (str/includes? (:message r) "flow of `handle`: s -> normalize -> respond -> result"))))

(deftest a-step-given-the-wrong-value-fails
  (let [r (spec/check 'writ.spec-demo.pipeline-spec
                      {:seed 42 :target 'writ.spec-demo.pipeline-swapped})
        fl (flow-of r 'handle)]
    (is (not (:ok r)))
    (is (= :ok (:status (first (filter #(= 'handle (:fn %)) (:calls r)))))
        "the call set is right...")
    (is (= :failed (:status fl)) "...but the data goes the wrong way")
    (is (str/includes? (:message r) "the flow of `handle` is not the one the spec gives"))
    (is (str/includes? (:message r) "`respond` is never given anything that comes from `normalize`"))
    (is (= ["`respond` is never given anything that comes from `normalize`"
            "what `handle` returns does not come from `normalize`"]
           (:errors fl))
        "respond's answer is still handle's; only the links that break are named")))

(deftest a-step-the-fn-never-calls-fails
  (let [r (spec/check 'writ.spec-demo.pipeline-spec
                      {:seed 42 :target 'writ.spec-demo.pipeline-bypass})]
    (is (not (:ok r)))
    (is (str/includes? (:message r) "`handle` never calls `respond`"))))

(deftest data-is-followed-through-lambdas-fns-by-name-and-loops
  (let [fl (spec/flow-facts 'writ.spec-demo.pipeline-many 'handle-all)]
    (is (some #(and (= 'normalize (:g %)) (some (fn [a] (contains? a [:param 0])) (:args %)))
              (:calls fl))
        "a lambda passed to map is given the collection's values")
    (is (some #(and (= 'respond (:g %)) (some (fn [a] (contains? a [:call 'normalize])) (:args %)))
              (:calls fl))
        "a fn passed by name is given the other arguments")
    (is (contains? (:result fl) [:call 'respond])))
  (let [fl (spec/flow-facts 'writ.spec-demo.pipeline-many 'count-ok)]
    (is (contains? (:result fl) [:call 'respond]) "a loop's result carries what its recur passed")
    (is (some #(and (= 'respond (:g %)) (some (fn [a] (contains? a [:param 0])) (:args %)))
              (:calls fl)))))

(deftest a-flow-form-is-checked-when-it-is-read
  (is (str/includes? (expansion-error '(writ.spec/flow handle [s] [s]))
                     "a chain needs at least two links"))
  (is (str/includes? (expansion-error '(writ.spec/flow handle [s] [:result s]))
                     "`:result` can only end a chain"))
  (is (str/includes? (expansion-error '(writ.spec/flow handle s [s normalize]))
                     "(flow f [param ...] [link link ...] ...)")))

(deftest a-flow-names-only-params-and-fns
  (let [r (spec/check 'writ.spec-demo.flow-unknown-spec {:seed 42})]
    (is (not (:ok r)))
    (is (str/includes? (:message r)
                       "flow of `handle` names `sanitize`, which is neither a parameter of `handle` nor a fn of writ.spec-demo.pipeline"))
    (is (str/includes? (:message r)
                       "flow of `handle` names 2 parameter(s), but `handle` takes 1"))))

(deftest calls-can-state-reach-instead-of-an-exact-set
  (let [r (spec/check 'writ.spec-demo.pipeline-layers-spec {:seed 42})]
    (is (:ok r) (:message r))
    (is (str/includes? (:message r) "`handle` goes through normalize, respond, valid?; never reaches clojure.string/upper-case")))
  (let [r (spec/check 'writ.spec-demo.pipeline-layers-spec
                      {:seed 42 :target 'writ.spec-demo.pipeline-inline})]
    (is (str/includes? (:message r) "`handle` does not reach `normalize`"))
    (is (not (str/includes? (:message r) "does not reach `respond`"))))
  (let [r (spec/check 'writ.spec-demo.pipeline-layers-spec
                      {:seed 42 :target 'writ.spec-demo.pipeline-upper})]
    (is (not (:ok r)))
    (is (str/includes? (:message r)
                       "`handle` reaches `clojure.string/upper-case`, which the spec says it never does: handle -> normalize -> clojure.string/upper-case"))))

(deftest a-shell-is-held-to-its-wiring
  (let [r (spec/check 'writ.spec-demo.shell-spec {:seed 42})]
    (is (not (:ok r)))
    (is (= :ok (:status (first (filter #(= 'writ.spec-demo.shell/serve (:fn %)) (:calls r))))))
    (is (= :ok (:status (flow-of r 'writ.spec-demo.shell/serve))))
    (is (str/includes? (:message r)
                       "`writ.spec-demo.shell/serve-raw` does not reach `writ.spec-demo.pipeline/handle`"))))
