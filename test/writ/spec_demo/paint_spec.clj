(ns writ.spec-demo.paint-spec
  "A workflow on the shape component, its code taking the component's
  data type apart: the static check knows Shape."
  (:require [writ.spec :refer [spec ann law graph]]))

(spec writ.spec-demo.paint {:uses [writ.spec-demo.shape-spec]})

(ann tins [Shape -> Nat])

(graph g {:states {:shape Shape, :tins Nat} :edges {:shape {[tins] #{:tins}}}})

(law a-circle-takes-one-more
  (forall [n Nat] (= (inc (writ.spec-demo.shape/area [:circle n])) (tins [:circle n]))))
