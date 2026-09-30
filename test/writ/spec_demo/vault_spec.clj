(ns writ.spec-demo.vault-spec
  "Who may take each step: a step anyone else tries is refused, and the
  vault stays as it was."
  (:require [writ.spec :refer [spec ann refine graph law]]))

(spec writ.spec-demo.vault)

(refine Role [r Keyword] (contains? #{:owner :clerk :guest} r))
(refine User [u {:id Nat, :role Role}] true)
(refine Open   [v (Tuple Keyword Nat)] (= :Open (first v)))
(refine Closed [v (Tuple Keyword Nat)] (= :Closed (first v)))

(ann deposit [(Tuple Keyword Nat) User Nat -> (Tuple Keyword Nat)])
(ann close   [(Tuple Keyword Nat) User -> (Tuple Keyword Nat)])

(graph vault
  {:start  [:open [:Open 0]]
   :actors {:type User :role :role}
   :states {:open Open, :closed Closed}
   :edges  {:open {[deposit User Nat] {:to #{:open} :by #{:owner :clerk}}
                   [close User]       {:to #{:closed} :by #{:owner}}}}
   :final  [:closed]})

(law a-deposit-adds-the-amount
  (forall [v Open, u User, n Nat]
    (=> (not= :guest (:role u)) (= (+ n (second v)) (second (deposit v u n))))))

(law a-closed-vault-holds-nothing
  (forall [v Open, u User] (=> (= :owner (:role u)) (= 0 (second (close v u))))))
