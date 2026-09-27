(ns writ.spec-demo.sort-pairs-spec
  "A spec whose helper destructures in a fn literal, which the prover
  cannot read."
  (:require [writ.spec :refer [spec ann law graph refine]]))

(spec writ.spec-demo.sort)

(ann insert [Nat (List Nat) -> (List Nat)])
(ann isort  [(List Nat) -> (List Nat)])

(refine Sorted [xs (List Nat)] (or (empty? xs) (apply <= xs)))

(graph sorting
  {:states {:unsorted (List Nat), :sorted Sorted}
   :edges  {:unsorted {[isort] #{:sorted}}
            :sorted   {[insert Nat _] #{:sorted}}}})

(defn in-order? [xs] (every? (fn [[a b]] (<= a b)) (partition 2 1 xs)))

(law sorted (forall [xs (List Nat)] (in-order? (isort xs))))
