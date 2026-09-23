(ns life.core-test
  "One spec, two implementations: life.core, written to be read, and
  life.fast, written to be fast. Both must meet it, and each broken one is
  turned away with the smallest world that shows the mistake."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [writ.spec :as spec]))

(defn- check [target]
  (spec/check 'life.core-spec {:target target :seed 42}))

(deftest the-readable-life-meets-the-spec
  (let [r (spec/check 'life.core-spec)]
    (is (:ok r) (:message r))))

(deftest the-fast-life-meets-the-same-spec
  (let [r (spec/check 'life.core-spec {:target 'life.fast})]
    (is (:ok r) (:message r))
    (is (= 'life.fast (:target r)))))

(deftest highlife-is-not-life
  (let [r (check 'life.broken.highlife)]
    (is (not (:ok r)))
    (is (str/includes? (:message r) "law `a-generation-follows-the-rule` fails for"))
    (testing "the world is shrunk to six cells, around a cell HighLife lets be born"
      (is (str/includes? (:message r) "(packed w) => #{[0 0] [1 0] [0 2] [2 0] [2 1] [0 1]}")))))

(deftest a-generation-updated-in-place-reads-its-own-future
  (let [r (check 'life.broken.in-place)]
    (is (not (:ok r)))
    (is (str/includes? (:message r) "(packed w) => #{[2 5] [0 5] [0 3]}"))
    (is (str/includes? (:message r) "(step (packed w)) => #{}"))
    (is (str/includes? (:message r) "(next-generation (packed w)) => #{[1 4]}"))))
