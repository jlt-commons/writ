(ns screens.core-test
  "The screen flow follows its transition table on all 42 screen and event
  pairs, and the table keeps its own rules. Each broken flow, and a draft
  of the table, is turned away with the pairs or paths that break."
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [writ.spec :as spec]))

(defn- check [target]
  (spec/check 'screens.core-spec {:target target :seed 42}))

(deftest the-screen-flow-follows-its-table
  (let [r (spec/check 'screens.core-spec)]
    (is (:ok r) (:message r))
    (is (str/includes? (:message r) "machine `screens`: 42 transitions checked"))))

(deftest back-must-resume-not-quit
  (let [m (first (:machines (check 'screens.broken.back-quits)))]
    (is (= '[{:state [:Paused] :event [:Back] :expected [:Gameplay] :actual [:Title]}]
           (:mismatches m)))))

(deftest a-global-pause-is-four-transitions-the-table-never-had
  (let [r (check 'screens.broken.pause-anywhere)]
    (is (= [[:Logo] [:Title] [:Options] [:Ending]]
           (map :state (:mismatches (first (:machines r))))))
    (is (str/includes? (:message r)
                       "(next-screen [:Title] [:Pause]) is [:Paused], but the table says [:Title] (no transition listed: the state stays)"))))

(deftest the-draft-table-breaks-its-own-rules
  (let [r (spec/check 'screens.draft-spec {:seed 42})]
    (testing "a screen with no way back"
      (is (str/includes? (:message r) "from [:Options] no final state can be reached")))
    (testing "a path to the logo after startup, shown step by step"
      (is (str/includes? (:message r)
                         (str "[:Title] must never lead to [:Logo], but it does: [:Title] -[:Confirm]-> "
                              "[:Gameplay] -[:Pause]-> [:Paused] -[:Quit]-> [:Logo]"))))))

(deftest the-table-draws-as-a-state-diagram
  (let [d (spec/mermaid 'screens.core-spec {:machine 'screens})]
    (is (str/includes? d "[*] --> Logo"))
    (is (str/includes? d "Paused --> Title : Quit"))
    (is (str/includes? d "Title --> [*]"))))
