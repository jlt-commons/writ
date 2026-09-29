(ns writ.spec-demo.account-redundant-spec
  "A guard with a clause that never fails on its own: an amount of type
  Nat is never negative, so (<= 0 amt) says nothing the type does not."
  (:require [writ.spec :refer [spec ann refine graph law question]]
            [writ.spec-demo.account :refer [withdraw close]]))

(spec writ.spec-demo.account)

(ann withdraw [(Tuple Keyword Int) Nat -> (Tuple Keyword Int)])
(ann close [(Tuple Keyword Int) -> (Tuple Keyword Int)])

(refine Open   [a (Tuple Keyword Int)] (and (= :Open (first a)) (<= 0 (second a))))
(refine Closed [a (Tuple Keyword Int)] (and (= :Closed (first a)) (zero? (second a))))

(graph account
  {:start  [:open [:Open 10]]
   :states {:open Open, :closed Closed}
   :edges  {:open {[withdraw Nat] {:to #{:open} :when (fn [a amt] (and (<= amt (second a)) (<= 0 amt))) :else :keep}
                   [close] #{:closed}}}
   :final  [:closed]})

(law withdraw-pays-out
  (forall [a Open, amt Nat]
    (=> (<= amt (second a)) (= (second (withdraw a amt)) (- (second a) amt)))))

