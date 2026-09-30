(ns writ.actors-test
  "Who may take a step: a graph names the argument that acts and the key
  that says its role, and an edge the roles that may take it.  Anyone
  else is refused, and the state stays as it was."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.string :as str]
            [writ.spec :as spec]))

(defn- has? [r s] (str/includes? (:message r) s))

(defn- law-result [report nm]
  (first (filter #(= nm (:law %)) (:laws report))))

(defn- expansion-error [form]
  (try (macroexpand-1 form) nil
       (catch Throwable e (ex-message e))))

(deftest permitted-steps-pass
  (let [r (spec/check 'writ.spec-demo.vault-spec {:seed 42})]
    (is (:ok r) (:message r))
    (is (#{:proved :tested} (:status (law-result r 'vault:open:close:refused))))))

(deftest a-step-taken-by-the-wrong-role-fails
  (let [r (spec/check 'writ.spec-demo.vault-spec {:seed 42 :target 'writ.spec-demo.vault-lax})]
    (is (not (:ok r)))
    (is (= :failed (:status (law-result r 'vault:open:close:refused))) (:message r))
    (is (has? r ":clerk"))))

(deftest the-plan-says-who-may-do-what
  (let [p (spec/plan 'writ.spec-demo.vault-spec)]
    (is (str/includes? p "who may do what"))
    (is (str/includes? p ":owner  deposit from open, close from open"))
    (is (str/includes? p ":clerk  deposit from open"))))

(deftest by-needs-actors-and-an-actor-argument
  (is (str/includes? (str (expansion-error '(writ.spec/graph g {:states {:a A} :edges {:a {[f User] {:to #{:a} :by #{:x}}}}})))
                     ":by needs the graph's :actors"))
  (is (str/includes? (str (expansion-error '(writ.spec/graph g {:actors {:type User :role :role}
                                                                 :states {:a A} :edges {:a {[f Nat] {:to #{:a} :by #{:x}}}}})))
                     "takes no User, so no one is there to act")))
