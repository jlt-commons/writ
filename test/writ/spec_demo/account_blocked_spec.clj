(ns writ.spec-demo.account-blocked-spec
  "An account spec with a blocking question: the next piece of work
  depends on the answer."
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
   :edges  {:open {[withdraw Nat] {:to #{:open} :when (fn [a amt] (<= amt (second a))) :else :keep}
                   [close] #{:closed}}}
   :final  [:closed]})

(law withdraw-pays-out
  (forall [a Open, amt Nat]
    (=> (<= amt (second a)) (= (second (withdraw a amt)) (- (second a) amt)))))

(question closing-fee "does closing an account charge a fee?" {:blocking true})
