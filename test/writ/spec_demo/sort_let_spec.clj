(ns writ.spec-demo.sort-let-spec
  "A law whose predicate binds a local with `let`."
  (:require [writ.spec :refer [spec ann law graph]]))

(spec writ.spec-demo.sort)

(ann insert [Nat (List Nat) -> (List Nat)])
(ann isort  [(List Nat) -> (List Nat)])

(graph sorting
  {:states {:item Nat, :unsorted (List Nat), :sorted (List Nat)}
   :edges  {:unsorted {[isort] #{:sorted}}
            :item     {[insert (List Nat)] #{:sorted}}}})

(law smallest-first
  (forall [xs (List Nat)]
    (=> (seq xs)
        (let [[a] (isort xs)] (= a (apply min xs))))))
