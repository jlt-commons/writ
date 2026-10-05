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
