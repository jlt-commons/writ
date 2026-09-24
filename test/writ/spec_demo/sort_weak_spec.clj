(ns writ.spec-demo.sort-weak-spec
  "A spec that states only that the output is ordered."
  (:require [writ.spec :refer [spec ann law graph refine]]))

(spec writ.spec-demo.sort)

(ann insert [Nat (List Nat) -> (List Nat)])
(ann isort  [(List Nat) -> (List Nat)])

(refine Sorted [xs (List Nat)] (or (empty? xs) (apply <= xs)))

(graph sorting
  {:states {:unsorted (List Nat), :sorted Sorted}
   :edges  {:unsorted {[isort] #{:sorted}}
            :sorted   {[insert Nat _] #{:sorted}}}})

(law sorted (forall [xs (List Nat)] (apply <= 0 (isort xs))))
