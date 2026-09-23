(ns pong.core-test
  "pong.core meets its spec, and each broken variant is turned away with a
  report that says what is wrong."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [writ.spec :as spec]))

(defn- check [target]
  (spec/check 'pong.core-spec {:target target :seed 42}))

(deftest pong-meets-its-spec
  (let [r (spec/check 'pong.core-spec)]
    (is (:ok r) (:message r))
    (testing "every signed fn is pinned down by the laws"
      (is (= [] (:gaps r))))))

(deftest a-draft-that-never-says-the-ball-moves-has-a-gap
  (let [r (spec/check 'pong.ball-draft-spec {:seed 42})]
    (is (not (:ok r)))
    (is (every? #(not= :failed (:status %)) (:laws r)) "every law holds...")
    (is (str/includes? (:message r)
                       "the spec does not pin down `advance`: every law still holds when it returns its argument `ball` unchanged")
        "...and still the spec is too weak")))

(deftest a-fast-ball-cannot-jump-the-paddle
  (let [r (check 'pong.broken.tunnel)]
    (is (not (:ok r)))
    (is (str/includes? (:message r) "law `the-left-paddle-stops-the-ball` fails for"))
    (testing "the counterexample is shrunk to a ball two cells from the paddle"
      (is (str/includes? (:message r) "(court-ball x y dx dy) => [3 44 -2 -2]"))
      (is (str/includes? (:message r) "=> [1 42 -2 -2]")))))

(deftest a-phase-step-forgets-is-caught-before-anything-runs
  (let [r (check 'pong.broken.forgot-pause)]
    (is (not (:ok (:static r))))
    (is (= [] (:laws r)))
    (is (str/includes? (:message r)
                       "the `case` on `phase` (Phase) does not handle :Paused"))))

(deftest a-rally-simulated-to-its-end-may-never-end
  (let [r (check 'pong.broken.endless-rally)]
    (is (not (:ok (:static r))))
    (is (str/includes? (:message r) "`recur` in `arrival-row` does not descend"))))
