(ns writ.spec-demo.parity-spec
  "An invariant on a plain state: a bump lands there with no refinement
  to check, so the invariant must be checked on its own."
  (:require [writ.spec :refer [spec ann refine graph invariant law]]))

(spec writ.spec-demo.parity)

(ann bump [Int -> Int])
(ann wrap [Int -> (Tuple Keyword Int)])

(refine Up [c (Tuple Keyword Int)] (= :Up (first c)))

(graph parity
  {:start  [:n 0]
   :states {:n Int, :up Up}
   :edges  {:n {[bump] #{:n}, [wrap] #{:up}}}
   :final  [:up]})

(invariant parity :n [n] (even? n))
(invariant parity :up [c] (even? (second c)))

(law bump-adds-one (forall [n Int] (= (inc n) (bump n))))
(law wrap-keeps-it (forall [n Int] (= n (second (wrap n)))))
