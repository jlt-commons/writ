(ns writ.evidence-test
  "A report says which laws are proved and which are only tested, and a
  spec can demand proof.  Tested is evidence, not proof: a spec that asks
  for proof fails while a law is only tested, unless that law says why it
  cannot be proved yet."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.string :as str]
            [writ.spec :as spec]))

(defn- law-result [report nm]
  (first (filter #(= nm (:law %)) (:laws report))))

(defn- expansion-error [form]
  (try (macroexpand-1 form) nil
       (catch Throwable e (ex-message e))))

(deftest every-law-says-whether-it-was-proved
  (let [r (spec/check 'writ.spec-demo.sort-spec {:seed 42})]
    (is (:ok r) (:message r))
    (testing "proof by the prover, by evaluating a closed law, or by a witness"
      (is (= :proof (:evidence (law-result r 'sorted))))
      (is (= :proof (:evidence (law-result r 'insert-empty))))
      (is (= :proof (:evidence (law-result r 'has-fixed-point)))))
    (testing "a law that only ran on generated inputs is tested"
      (is (= :test (:evidence (law-result r 'smallest-first)))))
    (testing "the report counts them"
      (is (= {:require :tested :proved 6 :tested 1 :laws 7} (:proof r)))
      (is (str/includes? (:message r) "6 of 7 laws proved"))
      (is (str/includes? (:message r) "tested, not proved: smallest-first")))))

(deftest a-check-can-demand-proof
  (let [r (spec/check 'writ.spec-demo.sort-spec {:seed 42 :require :proved})]
    (is (not (:ok r)))
    (is (= :unproved (:status (law-result r 'smallest-first))))
    (is (= :proved (:status (law-result r 'sorted))))
    (is (= :proved (:require (:proof r))))
    (testing "the message says what was required, what the prover said, and what to do"
      (is (str/includes? (:message r) "law `smallest-first` is tested, not proved, and the spec requires proof"))
      (is (str/includes? (:message r) "the prover:"))
      (is (str/includes? (:message r) ":because")))))

(deftest a-spec-demands-proof-and-a-law-may-say-why-it-is-only-tested
  (let [r (spec/check 'writ.spec-demo.sort-proved-spec {:seed 42})]
    (is (:ok r) (:message r))
    (is (= :proved (:require (:proof r))))
    (is (= {:require :tested :because "the prover has no model of min over a list yet"}
           (select-keys (law-result r 'smallest-first) [:require :because])))
    (testing "a law let off proof is always shown, with its reason"
      (is (str/includes? (:message r)
                         "law `smallest-first` is only tested: the prover has no model of min over a list yet")))))

(deftest a-law-can-demand-proof-in-a-tested-spec
  (let [r (spec/check 'writ.spec-demo.sort-unproved-spec {:seed 42})]
    (is (not (:ok r)))
    (is (= :unproved (:status (law-result r 'smallest-first))))
    (is (str/includes? (:message r) "law `smallest-first` is tested, not proved, and the law requires proof"))
    (testing "the other laws keep the spec's level: tested is enough for them"
      (is (= :tested (:status (law-result r 'sorted))))
      (is (= :proved (:status (law-result r 'permutation)))))))

(deftest proof-options-are-checked-when-the-spec-loads
  (is (str/includes? (expansion-error '(writ.spec/spec my.ns {:require :sure}))
                     ":require must be :proved or :tested"))
  (is (str/includes? (expansion-error '(writ.spec/spec my.ns {:strict true}))
                     "unknown options"))
  (is (str/includes? (expansion-error '(writ.spec/law l {:require :tested} (= 1 1)))
                     "needs :because"))
  (is (str/includes? (expansion-error '(writ.spec/law l {:because "x"} (= 1 1)))
                     ":because goes with :require :tested"))
  (is (str/includes? (expansion-error '(writ.spec/law l {:require :proved :why "x"} (= 1 1)))
                     "unknown options"))
  (is (nil? (expansion-error '(writ.spec/law l (= 1 1))))))
