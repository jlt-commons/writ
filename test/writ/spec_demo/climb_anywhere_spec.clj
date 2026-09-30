(ns writ.spec-demo.climb-anywhere-spec
  "The climb, but a run may start at any Up: nothing makes the first
  count even, so a climb may not assume it is."
  (:require [writ.spec :refer [spec ann refine graph invariant law]]))

(spec writ.spec-demo.climb)

(ann climb [(Tuple Keyword Int) -> (Tuple Keyword Int)])

(refine Up [c (Tuple Keyword Int)] (= :Up (first c)))

(graph climbing
  {:start  :up
   :states {:up Up}
   :edges  {:up {[climb] #{:up}}}
   :final  [:up]})

(invariant climbing :up [c] (even? (second c)))

(law a-climb-adds-two
  (forall [c Up] (= (+ 2 (second c)) (second (climb c)))))
