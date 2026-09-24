(ns writ.spec-demo.sort-every-spec
  "A law that passes a fn literal to every?."
  (:require [writ.spec :refer [spec ann law graph]]))

(spec writ.spec-demo.sort)

(ann insert [Nat (List Nat) -> (List Nat)])
(ann isort  [(List Nat) -> (List Nat)])

(graph sorting
  {:states {:item Nat, :unsorted (List Nat), :sorted (List Nat)}
   :edges  {:unsorted {[isort] #{:sorted}}
            :item     {[insert (List Nat)] #{:sorted}}}})

(law every-prefix-starts-low
  (forall [xs (List Nat)]
    (every? #(<= (first (isort xs)) %) xs)))
