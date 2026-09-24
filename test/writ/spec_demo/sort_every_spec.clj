(ns writ.spec-demo.sort-every-spec
  "A law that passes a fn literal to every?."
  (:require [writ.spec :refer [spec ann law graph refine]]))

(spec writ.spec-demo.sort)

(ann insert [Nat (List Nat) -> (List Nat)])
(ann isort  [(List Nat) -> (List Nat)])

(refine Sorted [xs (List Nat)] (or (empty? xs) (apply <= xs)))

(graph sorting
  {:states {:unsorted (List Nat), :sorted Sorted}
   :edges  {:unsorted {[isort] #{:sorted}}
            :sorted   {[insert Nat _] #{:sorted}}}})

(law every-prefix-starts-low
  (forall [xs (List Nat)]
    (every? #(<= (first (isort xs)) %) xs)))
