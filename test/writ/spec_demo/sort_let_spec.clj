(ns writ.spec-demo.sort-let-spec
  "A law whose predicate binds a local with `let`."
  (:require [writ.spec :refer [spec ann law graph refine]]))

(spec writ.spec-demo.sort)

(ann insert [Nat (List Nat) -> (List Nat)])
(ann isort  [(List Nat) -> (List Nat)])

(refine Sorted [xs (List Nat)] (or (empty? xs) (apply <= xs)))

(graph sorting
  {:states {:unsorted (List Nat), :sorted Sorted}
   :edges  {:unsorted {[isort] #{:sorted}}
            :sorted   {[insert Nat _] #{:sorted}}}})

(law smallest-first
  (forall [xs (List Nat)]
    (=> (seq xs)
        (let [[a] (isort xs)] (= a (apply min xs))))))
