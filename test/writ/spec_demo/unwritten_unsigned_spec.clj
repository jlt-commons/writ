(ns writ.spec-demo.unwritten-unsigned-spec
  "An example of a fn the spec forgot to sign, before any code."
  (:require [writ.spec :refer [spec ann law graph example]]))

(spec writ.spec-demo.unwritten-unsigned)

(ann total [(Vec Nat) -> Nat])

(graph till {:states {:items (Vec Nat), :sum Nat} :edges {:items {[total] #{:sum}}}})

(example total [[1 2]] 3)
(example bump [1] 2)

(law total-adds (forall [xs (Vec Nat)] (= (reduce + 0 xs) (total xs))))
