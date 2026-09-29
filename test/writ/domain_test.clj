(ns writ.domain-test
  "What a spec says about the problem's domain beyond single laws: what
  each state always holds, runs through the real steps, the guard under
  which a step is taken and what happens when it is refused, the
  questions a spec leaves open, its obligations as data, a record that
  shows when a spec got weaker, and laws no code could satisfy together."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.string :as str]
            [writ.hash]
            [writ.spec :as spec]))

(defn- law-result [report nm]
  (first (filter #(= nm (:law %)) (:laws report))))

(defn- expansion-error [form]
  (try (macroexpand-1 form) nil
       (catch Throwable e (ex-message e))))

(defn- has? [r s] (str/includes? (:message r) s))

;; --- invariants and runs ----------------------------------------------------------

(deftest an-invariant-must-name-a-graph-of-the-spec
  (let [r (spec/check 'writ.spec-demo.gauge-stray-spec {:seed 42})]
    (is (not (:ok r)))
    (is (has? r "invariant `gauges :hot` names a graph the spec does not have"))))

(deftest an-invariant-the-state-already-says-is-vacuous
  (let [r (spec/check 'writ.spec-demo.gauge-vacuous-spec {:seed 42})]
    (is (not (:ok r)))
    (is (has? r "invariant `gauge :hot` is vacuous"))))

(deftest runs-must-reach-every-final-state
  (let [r (spec/check 'writ.spec-demo.gauge-shallow-spec {:seed 42})]
    (is (not (:ok r)))
    (is (has? r "no run of 5 reached :cold"))))

(deftest a-loop-that-never-finishes-is-shown
  (let [r (spec/check 'writ.spec-demo.spin-spec {:seed 42})]
    (is (not (:ok r)))
    (is (has? r "from :a no final state can be reached"))
    (is (has? r "it loops :a -> :b -> :a"))))

;; --- guarded edges ----------------------------------------------------------------

(deftest a-guarded-edge-is-taken-under-its-guard-and-refused-otherwise
  (let [r (spec/check 'writ.spec-demo.account-spec {:seed 42})]
    (is (:ok r) (:message r))
    (is (#{:proved :tested} (:status (law-result r 'account:open:withdraw))))
    (is (#{:proved :tested} (:status (law-result r 'account:open:withdraw:refused))))
    (is (= :witnessed (:status (law-result r 'account:open:withdraw:when))))))

(deftest a-refused-step-must-keep-the-state
  (let [r (spec/check 'writ.spec-demo.account-spec {:seed 42 :target 'writ.spec-demo.account-lossy})]
    (is (not (:ok r)))
    (is (= :failed (:status (law-result r 'account:open:withdraw:refused))))
    (is (has? r "when its guard fails"))
    (is (has? r "though its guard fails there and it must leave it as it was"))))

(deftest a-guard-that-never-holds-fails
  (let [r (spec/check 'writ.spec-demo.account-never-spec {:seed 42})]
    (is (not (:ok r)))
    (is (= :failed (:status (law-result r 'account:open:withdraw:when))))
    (is (has? r "the guard of withdraw from open never holds"))))

(deftest each-clause-of-a-guard-must-fail-on-its-own
  (let [r (spec/check 'writ.spec-demo.account-redundant-spec {:seed 42})]
    (is (not (:ok r)))
    (is (has? r "(<= 0 amt)"))
    (is (has? r "never fails on its own"))))

(deftest a-guarded-edge-is-checked-for-shape
  (is (str/includes? (expansion-error '(writ.spec/graph g {:states {:a A} :edges {:a {[f] {:when (fn [s] true)}}}}))
                     "needs a set of target states"))
  (is (str/includes? (expansion-error '(writ.spec/graph g {:states {:a A} :edges {:a {[f] {:to #{:a} :when true}}}}))
                     ":when (fn [state arg ...] test)"))
  (is (str/includes? (expansion-error '(writ.spec/graph g {:states {:a A} :edges {:a {[f Nat] {:to #{:a} :when (fn [s] true)}}}}))
                     "takes the fn's 2 argument(s)"))
  (is (str/includes? (expansion-error '(writ.spec/graph g {:states {:a A} :edges {:a {[f] {:to #{:a} :when (fn [s] true) :else :z}}}}))
                     ":else is :keep")))

;; --- open questions ---------------------------------------------------------------

(deftest an-open-question-is-reported
  (let [r (spec/check 'writ.spec-demo.account-question-spec {:seed 42})]
    (is (:ok r) (:message r))
    (is (= '[overdraft] (mapv :id (:questions r))))
    (is (has? r "open question `overdraft`"))))

(deftest a-blocking-question-fails-the-check
  (let [r (spec/check 'writ.spec-demo.account-blocked-spec {:seed 42})]
    (is (not (:ok r)))
    (is (has? r "the spec is not finished"))
    (is (has? r "closing-fee"))))

(deftest a-question-is-checked-for-shape
  (is (str/includes? (expansion-error '(writ.spec/question "q" "why?")) "simple symbol"))
  (is (str/includes? (expansion-error '(writ.spec/question q "")) "needs the question"))
  (is (str/includes? (expansion-error '(writ.spec/question q "why?" {:urgent true})) ":blocking")))

(deftest the-plan-shows-open-questions
  (is (str/includes? (spec/plan 'writ.spec-demo.account-blocked-spec)
                     "open questions\n  closing-fee (blocking): does closing an account charge a fee?")))

;; --- obligations ------------------------------------------------------------------

(deftest obligations-come-from-the-spec-alone
  (let [os (spec/obligations 'writ.spec-demo.account-spec)
        ids (set (map :id os))]
    (is (every? ids ["law.withdraw-pays-out"
                     "edge.account.open.withdraw"
                     "step.account.open.withdraw.open"
                     "guard.account.open.withdraw"
                     "refused.account.open.withdraw"
                     "edge.account.open.close"
                     "reach.account"
                     "final.account"
                     "signature.withdraw"])
        (pr-str (sort ids)))
    (is (every? :kind os))
    (is (= '#{withdraw} (set (:fns (first (filter #(= "refused.account.open.withdraw" (:id %)) os))))))))

(deftest obligations-include-invariants-and-questions
  (let [ids (set (map :id (spec/obligations 'writ.spec-demo.gauge-spec)))]
    (is (contains? ids "invariant.gauge.hot")))
  (let [ids (set (map :id (spec/obligations 'writ.spec-demo.account-blocked-spec)))]
    (is (contains? ids "question.closing-fee"))))

(deftest a-check-reports-each-obligation
  (let [r (spec/check 'writ.spec-demo.account-spec {:seed 42})
        ids (set (map :id (spec/obligations 'writ.spec-demo.account-spec)))
        seen (into {} (map (juxt :id :status)) (:obligations r))]
    (is (= ids (set (keys seen))))
    (is (every? #{:met} (vals seen)) (pr-str seen))))

;; --- records and attest -----------------------------------------------------------

(def ^:private record-path "/tmp/writ-domain-record.edn")

(deftest sha256-matches-the-standard
  (is (= "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" (writ.hash/sha256 "abc")))
  (is (= "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855" (writ.hash/sha256 ""))))

(deftest a-record-carries-hashes-and-each-law
  (spec/check 'writ.spec-demo.account-spec {:seed 42 :record record-path})
  (let [rec (read-string (slurp record-path))]
    (is (every? #(re-matches #"[0-9a-f]{64}" %) (vals (select-keys (:hashes rec) [:spec :target]))))
    (is (= '(forall [a Open amt Nat]
              (=> (<= amt (second a)) (= (second (withdraw a amt)) (- (second a) amt))))
           (:prop (first (filter #(= 'withdraw-pays-out (:law %)) (:laws rec))))))))

(defn- rec [& laws]
  {:ok true :hashes {:spec "a" :target "b"} :questions []
   :laws (vec (for [[nm prop status evidence req] laws]
                {:law nm :prop prop :status status :evidence evidence :require req}))})

(deftest attest-accepts-the-same-spec
  (let [r (rec ['a '(p x) :proved :proof :proved])]
    (is (:ok (spec/attest r r)))))

(deftest attest-names-each-way-a-spec-got-weaker
  (let [old (rec ['a '(p x) :proved :proof :proved]
                 ['b '(q x) :proved :proof :proved]
                 ['c '(r x) :proved :proof :proved]
                 ['d '(s x) :proved :proof :proved])
        new (rec ['a '(p x) :tested :test :tested]
                 ['b '(q y) :proved :proof :proved]
                 ['d '(s x) :tested :test :proved])
        w (spec/attest old new)
        by (into {} (map (juxt :law :what)) (:weakened w))]
    (is (not (:ok w)))
    (is (= :require-lowered (get by 'a)))
    (is (= :restated (get by 'b)))
    (is (= :removed (get by 'c)))
    (is (= :evidence-dropped (get by 'd)))))

(deftest attest-catches-a-downgraded-question
  (let [old (assoc (rec) :questions [{:id 'q :blocking true}])
        new (assoc (rec) :questions [{:id 'q :blocking false}])]
    (is (= [{:question 'q :what :no-longer-blocking}]
           (:weakened (spec/attest old new))))))

(deftest attest-reruns-the-check-rather-than-trust-the-record
  (spit record-path (pr-str (assoc (rec) :ok true :spec 'writ.spec-demo.balance-spec)))
  (let [w (spec/attest record-path 'writ.spec-demo.balance-spec)]
    (is (not (:ok w)))
    (is (some #(= :claimed-pass (:what %)) (:weakened w)))))

;; --- contradicting laws -----------------------------------------------------------

(deftest laws-that-contradict-are-named-together
  (let [r (spec/check 'writ.spec-demo.balance-spec {:seed 42})]
    (is (not (:ok r)))
    (is (= '[[rises falls]] (mapv :laws (:contradictions r))))
    (is (has? r "laws `rises` and `falls` cannot both hold"))))

(deftest failing-laws-that-agree-are-not-a-contradiction
  (let [r (spec/check 'writ.spec-demo.gauge-spec {:seed 42 :target 'writ.spec-demo.gauge-bad})]
    (is (not (:ok r)))
    (is (empty? (:contradictions r)))))
