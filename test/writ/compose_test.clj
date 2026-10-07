(ns writ.compose-test
  "A spec built on another: the component taken at its spec."
  (:require [clojure.test :refer [deftest is]]
            [clojure.string :as str]
            [clojure.java.io :as io]
            [writ.book :as book]
            [writ.prove :as prover]
            [writ.spec :as spec]))

(defn- has? [r s] (str/includes? (:message r) s))
(defn- law-result [r nm] (first (filter #(= nm (:law %)) (:laws r))))

(deftest a-workflow-is-proved-from-its-components-laws
  (let [r (spec/check 'writ.spec-demo.shop-spec {:seed 7})]
    (is (:ok r) (:message r))
    (is (= :proved (:status (law-result r 'a-wrong-password-pays-nothing))))
    (is (has? r "are taken at that spec"))))

(deftest a-workflow-that-breaks-a-components-requires-fails
  (let [r (spec/check 'writ.spec-demo.shop-spec {:seed 7 :target 'writ.spec-demo.shop-eager})]
    (is (not (:ok r)))
    (is (has? r "`writ.spec-demo.auth/charge` requires (authed? s)") (:message r))))

(deftest a-workflow-on-a-failing-component-fails
  (let [r (spec/check 'writ.spec-demo.shop-on-strict-spec {:seed 7})]
    (is (not (:ok r)))
    (is (has? r "builds on writ.spec-demo.auth-strict-spec, which fails its own check") (:message r))))

(deftest a-refinement-that-only-names-a-record-is-a-plain-state
  (let [r (spec/check 'writ.spec-demo.auth-spec {:seed 7})]
    (is (:ok r) (:message r))))

(deftest a-workflow-names-its-components-types
  (let [r (spec/check 'writ.spec-demo.shop-typed-spec {:seed 7})]
    (is (:ok r) (:message r))))

;; --- what the prover reads ---------------------------------------------------------

(deftest a-store-of-named-records-is-proved
  (let [r (spec/check 'writ.spec-demo.lockout-spec {:seed 7})]
    (is (:ok r) (:message r))))

(deftest a-pipeline-is-proved-by-position
  (let [r (spec/check 'writ.spec-demo.tags-spec {:seed 7})]
    (is (:ok r) (:message r))
    (is (re-find #"element by element" (str (:proof (law-result r 'tagging-keeps-the-weights)))))))

(deftest a-workflow-is-proved-to-meet-its-components-requires
  (let [r (spec/check 'writ.spec-demo.shop-spec {:seed 7})
        l (law-result r 'checkout:keeps-requires)]
    (is (= :proved (:status l)) (:message r))
    (is (some #(re-find #"auth-spec" (str %)) (:lemmas (law-result r 'a-wrong-password-pays-nothing)))
        "proved from the component's law, its code left folded")))

(defn- keeps-requires? [n]
  (let [forms (book/read-forms (io/resource (str (-> (str n) (str/replace "." "/") (str/replace "-" "_")) ".clj")))
        sess '{:user String :authed Bool}
        q #(symbol "writ.spec-demo.auth" %)
        sigs {(symbol (str n) "checkout") {:params '[(Map String String) String String Nat] :ret 'Nat}
              (q "login") {:params ['(Map String String) 'String 'String] :ret sess}
              (q "authed?") {:params [sess] :ret 'Bool}
              (q "charge") {:params [sess 'Nat] :ret 'Nat}}
        names (into {} (for [f ["login" "authed?" "charge"] k [(symbol "auth" f) (q f)]] [k (q f)]))
        [defs own] (prover/definitions [[n forms names]] sigs)]
    (:proved (prover/prove-law
               {:prop (list 'forall '[accounts (Map String String)]
                            (list 'forall '[user String]
                                  (list 'forall '[password String]
                                        (list 'forall '[total Nat]
                                              (list 'vector? [(list (symbol (str n) "checkout") 'accounts 'user 'password 'total)])))))
                :defs defs :target n :own (merge names own) :sigs sigs :tenv {} :total true
                :rets (into {} (for [[f s] sigs] [f (:ret s)]))
                :trusted-rets (into {} (for [f ["login" "authed?" "charge"]] [(q f) (:ret (get sigs (q f)))]))
                :component-requires {(q "charge") {:params '[s amount] :body (list (q "authed?") 's)}}}))))

(deftest a-call-that-may-break-a-components-requires-is-not-proved
  (is (keeps-requires? 'writ.spec-demo.shop) "it charges only an authenticated session")
  (is (not (keeps-requires? 'writ.spec-demo.shop-eager))
      "it charges before it looks, though it uses the charge only after"))

(deftest a-test-of-the-code-the-laws-take-one-way-is-named
  (let [r (spec/check 'writ.spec-demo.fee-spec {:seed 1})]
    (is (some #(re-find #"`fee`: \(> n \(\* 40 40\)\) was never true" %) (:one-way-tests r)) (pr-str (:one-way-tests r)))
    (is (re-find #"no law took both ways" (:message r)))))

(deftest an-operand-that-never-decides-alone-is-named
  (let [r (spec/check 'writ.spec-demo.admit-spec {:seed 1})]
    (is (some #(re-find #"`admit`: in \(and \(<= 18 age\) member\), \(<= 18 age\) was never false while the others were true" %)
              (:one-way-tests r))
        (pr-str (:one-way-tests r)))
    (is (not-any? #(re-find #", member was never" %) (:one-way-tests r))
        "a non-member is tried with an adult's age")))

(deftest a-step-is-taken-only-where-its-fn-requires-allow
  (let [r (spec/check 'writ.spec-demo.purse-spec {:seed 1})]
    (is (:ok r) (:message r))
    (is (some #(= 'wallet:purse:spend:refused (:law %)) (:laws r)))))

(deftest a-max-whose-other-side-never-wins-is-named
  (let [r (spec/check 'writ.spec-demo.fee-spec {:seed 1})]
    (is (some #(re-find #"`floor-fee`: \(>= 10 \(quot n 100\)\) was never false" %) (:one-way-tests r))
        (pr-str (:one-way-tests r)))))

(deftest a-workflow-lands-in-its-components-refinement
  (let [r (spec/check 'writ.spec-demo.hits-user-spec {:seed 3})]
    (is (:ok r) (:message r))
    (is (= :proved (:status (law-result r 'twice:hits:add-twice))) (:message r))))

(deftest a-test-made-of-an-and-is-named-as-the-code-wrote-it
  (let [r (spec/check 'writ.spec-demo.gate-spec {:seed 7 :adequacy false})]
    (is (some #(str/includes? % "(and (<= 18 age) member?) was never true") (:one-way-tests r))
        (pr-str (:one-way-tests r)))
    (is (not (str/includes? (:message r) "-combo")) (:message r))))

(deftest a-fold-over-nothing-is-proved-whatever-its-step
  (let [r (spec/check 'writ.spec-demo.fold-spec {:seed 7 :adequacy false})]
    (is (:ok r) (:message r))
    (is (= :proved (:status (law-result r 'nothing-runs-nothing))) (:message r))))

(deftest a-workflow-takes-apart-its-components-data
  (let [r (spec/check 'writ.spec-demo.paint-spec {:seed 7 :adequacy false})]
    (is (:ok r) (:message r))))

(deftest laws-over-tagged-data-are-proved
  ;; simplifying-keeps-the-value by induction, each step case cross-
  ;; fertilised: its (evaluate a env) put back as (evaluate (simplify a) env)
  (let [r (spec/check 'writ.spec-demo.arith-spec {:seed 7 :adequacy false})]
    (is (:ok r) (:message r))
    (doseq [l '[evaluate-add evaluate-mul times-zero-is-zero plus-zero-is-itself two-negations-cancel
                simplifying-keeps-the-value
                simplify-makes-a-normal-form simplify-leaves-a-normal-form
                simplifying-twice-is-simplifying-once]]
      (is (= :proved (:status (law-result r l))) (str l)))
    ;; a case over a closed type always matches: its last test is no note
    (is (not-any? #(re-find #"identical\?" %) (:one-way-tests r)) (pr-str (:one-way-tests r)))))

(deftest two-types-may-share-a-constructor-name
  (let [r (spec/check 'writ.spec-demo.calc-spec {:seed 7 :adequacy false})]
    (is (:ok r) (:message r))))

(deftest a-scan-opens-its-clauses-a-step-at-a-time
  ;; clause-of on an empty clause list opens though its message is (nth msgs
  ;; i), and a binding a case reads first needs no strict marker: otherwise
  ;; each induction step unrolls the scan until the fuel runs out
  (let [r (spec/check 'writ.spec-demo.mailbox-spec {:seed 7 :adequacy false})]
    (is (:ok r) (:message r))
    (doseq [l '[nothing-matches a-take-is-a-clause-taking-a-message
                a-scan-that-takes-nothing-stops-at-the-end]]
      (is (= :proved (:status (law-result r l))) (str l)))))

(deftest a-place-read-from-a-list-it-is-inside-is-typed
  ;; (nth cs-t (- i 1)) under (<= 1 i) (<= i (count cs-t)) is an element,
  ;; and index-of, which passes its id on as it is, opens on it
  (let [r (spec/check 'writ.spec-demo.roster-spec {:seed 7 :adequacy false})]
    (is (:ok r) (:message r))
    (is (= :proved (:status (law-result r 'a-child-present-has-an-index))) (:message r))))

(deftest a-literal-pattern-against-a-mailbox-message-stays-folded
  ;; (capture p-a (nth msgs i)) is split on as one condition: opened on the
  ;; literal, it takes the message apart a split per level
  (let [r (spec/check 'writ.spec-demo.receive-spec {:seed 7 :adequacy false})]
    (is (:ok r) (:message r))
    (is (= :proved (:status (law-result r 'scan-is-the-manual))) (:message r))))

(deftest a-refined-field-is-read-as-its-base-type
  ;; the prover knows no refinement by name: a field of one, unread, kept
  ;; (= t-h t-h) from closing an induction step
  (let [r (spec/check 'writ.spec-demo.alarms-spec {:seed 7 :adequacy false})]
    (is (:ok r) (:message r))
    (is (= :proved (:status (law-result r 'cancelling-what-is-not-there-changes-nothing))) (:message r))))

(deftest a-recursion-down-a-vector-of-unknown-length-stops
  ;; tuple-binders on a (Vec Symbol) of unknown length: unfolded on, each
  ;; level's alternatives merged into the next and ran the heap out in
  ;; minutes; it stops as a recursion on a value of unknown shape does
  (let [r (spec/check 'writ.spec-demo.binders-spec {:seed 7 :adequacy false :cache false})]
    (is (:ok r) (:message r))
    (is (< (:prover (:timings r)) 30000) (pr-str (:timings r)))))
