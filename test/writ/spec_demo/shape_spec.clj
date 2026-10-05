(ns writ.spec-demo.shape-spec
  "A component with a data type of its own."
  (:require [writ.spec :refer [spec data ann law graph]]))

(spec writ.spec-demo.shape {:test false})

(data Shape (circle Nat) (square Nat))

(ann area [Shape -> Nat])

(graph g {:states {:shape Shape, :area Nat} :edges {:shape {[area] #{:area}}}})

(law a-square-is-its-side-squared (forall [n Nat] (= (* n n) (area [:square n]))))
