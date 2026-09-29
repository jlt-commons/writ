(ns writ.spec-demo.account-never-spec
  "A guard no withdrawal can pass: the amount would have to be both
  over five and under three."
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
   :edges  {:open {[withdraw Nat] {:to #{:open} :when (fn [a amt] (and (> amt 5) (< amt 3))) :else :keep}
                   [close] #{:closed}}}
   :final  [:closed]})

(law withdraw-pays-out
  (forall [a Open, amt Nat]
    (=> (<= amt (second a)) (= (second (withdraw a amt)) (- (second a) amt)))))

