(ns writ.spec-demo.sort-weak-spec
  "A spec that states only that the output is ordered."
  (:require [writ.spec :refer [spec ann law]]))

(spec writ.spec-demo.sort)

(ann insert [Nat (List Nat) -> (List Nat)])
(ann isort  [(List Nat) -> (List Nat)])

(law sorted (forall [xs (List Nat)] (apply <= 0 (isort xs))))
