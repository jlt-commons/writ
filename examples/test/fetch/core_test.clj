(ns fetch.core-test
  "The retry policy meets its constraints, and a spec made of examples is
  shown to say too little."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [writ.spec :as spec]))

(defn- check [target]
  (spec/check 'fetch.core-spec {:target target :seed 42}))

(deftest the-retry-policy-meets-its-spec
  (let [r (spec/check 'fetch.core-spec)]
    (is (:ok r) (:message r))))

(deftest a-spec-of-examples-leaves-every-other-status-open
  (let [r (spec/check 'fetch.examples-spec {:seed 42})]
    (is (every? #(= :evaluated (:status %)) (:laws r)) "every example holds...")
    (is (str/includes? (:message r)
                       (str "the spec does not pin down `classify`: every law still holds when it "
                            "returns a different value whenever `status` is not one of 200, 301, 404, 429, 503"))
        "...and that is all the spec says")))

(deftest a-wait-with-no-cap-is-caught-where-it-first-passes-the-cap
  (let [r (check 'fetch.broken.uncapped)]
    (is (str/includes? (:message r) "law `a-wait-is-positive-and-capped` fails for\n  a = 6"))
    (is (str/includes? (:message r) "(backoff-ms a) => 16000"))))

(deftest a-post-the-server-may-have-applied-is-not-sent-twice
  (let [r (check 'fetch.broken.post-retry)]
    (is (str/includes? (:message r) "law `a-post-is-sent-again-only-when-the-server-refused-it` fails"))
    (testing "shrunk to a POST that got no response at all"
      (is (str/includes? (:message r) "(one-of transient i) => 0"))
      (is (str/includes? (:message r) "(next-action :post (one-of transient i) a) => [:Wait 250]")))))
