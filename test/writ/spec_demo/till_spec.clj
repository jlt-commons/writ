(ns writ.spec-demo.till-spec
  "Who may take a step and when: a role and a guard of the edge's own."
  (:require [writ.spec :refer [spec ann refine graph law]]))

(spec writ.spec-demo.till)

(refine Role [r Keyword] (contains? #{:owner :clerk :guest} r))
(refine User [u {:id Nat, :role Role}] true)
(refine Open [t (Tuple Keyword Nat)] (= :Open (first t)))

(ann pay-in [(Tuple Keyword Nat) User Nat -> (Tuple Keyword Nat)])

(graph till
  {:start  [:open [:Open 0]]
   :actors {:type User :role :role}
   :states {:open Open}
   :edges  {:open {[pay-in User Nat] {:to #{:open} :by #{:owner :clerk}
                                      :when (fn [t u amt] (and (pos? amt) (<= amt 100)))}}}
   :final  [:open]})

(law paying-in-adds-the-amount
  (forall [t Open, u User, n Nat]
    (=> (and (not= :guest (:role u)) (pos? n) (<= n 100))
        (= (+ n (second t)) (second (pay-in t u n))))))
