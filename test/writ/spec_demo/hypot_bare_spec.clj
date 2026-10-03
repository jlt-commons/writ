(ns writ.spec-demo.hypot-bare-spec
  "The hypot spec without its assumptions: the host members are interop."
  (:require [writ.spec :refer [spec ann law]]))

(spec writ.spec-demo.hypot {:require :tested})

(ann hypot [Double Double -> Double])
(ann norm  [Double Double -> Double])

(law hypot-is-symmetric
  (forall [x Double y Double] (= (hypot x y) (hypot y x))))
