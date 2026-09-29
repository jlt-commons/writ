(ns writ.spec-demo.climb-spec
  "An invariant that holds by induction only: a climb keeps an even count
  even, but takes an odd one to an odd one."
  (:require [writ.spec :refer [spec ann refine graph invariant law]]))

(spec writ.spec-demo.climb)

(ann climb [(Tuple Keyword Int) -> (Tuple Keyword Int)])

(refine Up [c (Tuple Keyword Int)] (= :Up (first c)))

(graph climbing
  {:start  [:up [:Up 0]]
   :states {:up Up}
   :edges  {:up {[climb] #{:up}}}
   :final  [:up]})

(invariant climbing :up [c] (even? (second c)))

(law a-climb-adds-two
  (forall [c Up] (= (+ 2 (second c)) (second (climb c)))))
