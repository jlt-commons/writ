(ns writ.entity-test
  "Many entities: a collection of records keyed by a field, with fields
  no two of them share, and invariants kept by every step because they
  held before it."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.string :as str]
            [writ.spec :as spec]
            [writ.kind :as kind]))

(defn- has? [r s] (str/includes? (:message r) s))

(defn- law-result [report nm]
  (first (filter #(= nm (:law %)) (:laws report))))

(def ^:private member '{:id Nat, :email String})

(deftest an-index-is-keyed-by-its-field
  (let [vs (spec/sample (list 'Index :id member) {} 60)]
    (is (every? map? vs))
    (is (some seq vs))
    (is (every? (fn [db] (every? (fn [[k v]] (= k (:id v))) db)) vs))))

(deftest unique-fields-are-distinct-across-the-records
  (let [vs (spec/sample (list 'Index :id member :unique [:email]) {} 100)]
    (is (every? (fn [db] (apply distinct? nil (map :email (vals db)))) vs))
    (is (some #(< 1 (count %)) vs))))

(deftest an-index-conforms-by-key-and-uniqueness
  (let [t (list 'Index :id member :unique [:email])]
    (is (spec/conforms? t {} {}))
    (is (spec/conforms? t {1 {:id 1 :email "a"} 2 {:id 2 :email "b"}} {}))
    (is (not (spec/conforms? t {1 {:id 2 :email "a"}} {})) "the key is not the record's id")
    (is (not (spec/conforms? t {1 {:id 1 :email "a"} 2 {:id 2 :email "a"}} {})) "two share an email")
    (is (not (spec/conforms? t {1 {:id 1}} {})) "a record missing a key")))

(deftest an-index-is-a-well-formed-type
  (is (kind/check-type (list 'Index :id member :unique [:email]) {} #{}))
  (is (thrown-with-msg? Exception #"\(Index :key Record\)"
        (kind/check-type (list 'Index 'id member) {} #{})))
  (is (thrown-with-msg? Exception #"keys each record by :uid, which the record does not have"
        (kind/check-type (list 'Index :uid member) {} #{})))
  (is (thrown-with-msg? Exception #":unique names :mail, which the record does not have"
        (kind/check-type (list 'Index :id member :unique [:mail]) {} #{}))))

(deftest unique-by-is-true-of-no-two-alike
  (is (spec/unique-by? :email []))
  (is (spec/unique-by? :email [{:email "a"} {:email "b"}]))
  (is (not (spec/unique-by? :email [{:email "a"} {:email "a"}]))))

(deftest a-registry-keeps-its-rule-across-members
  (let [r (spec/check 'writ.spec-demo.registry-spec {:seed 42})]
    (is (:ok r) (:message r))))

(deftest a-step-that-breaks-the-rule-across-members-fails
  (let [r (spec/check 'writ.spec-demo.registry-spec {:seed 42 :target 'writ.spec-demo.registry-dup})]
    (is (not (:ok r)))
    (is (= :failed (:status (law-result r 'registry:db:register))) (:message r))))

(deftest an-invariant-holds-by-induction
  (testing "an edge may assume the invariants of the state it leaves"
    (let [r (spec/check 'writ.spec-demo.climb-spec {:seed 42})]
      (is (:ok r) (:message r))
      (is (#{:proved :tested} (:status (law-result r 'climbing:up:climb)))))))
