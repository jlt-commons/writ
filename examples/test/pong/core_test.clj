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

(deftest pong-is-proved
  (let [r (spec/check 'pong.core-spec {:seed 42 :adequacy false})]
    (is (= (:laws (:proof r)) (+ (:proved (:proof r)))) (:message r))
    (is (str/includes? (:message r) "graph `pong`: 4 edges proved"))))

(deftest a-fast-ball-cannot-jump-the-paddle
  (let [r (check 'pong.broken.tunnel)]
    (is (not (:ok r)))
    (is (str/includes? (:message r) "law `the-left-paddle-stops-the-ball` fails for"))
    (testing "no test finds it; the solver does, with a ball two cells from the paddle"
      (is (str/includes? (:message r) "b  = [3 3 -2 0]"))
      (is (str/includes? (:message r) "(advance b ly ry) => [1 3 -2 0]"))
      (is (str/includes? (:message r) "found by the solver")))))

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
