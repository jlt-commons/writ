(ns writ.spec-demo.hypot-wrong-spec
  "An assumed host member typed wrong for its call."
  (:require [writ.spec :refer [spec ann law assume]]))

(spec writ.spec-demo.hypot {:require :tested})

(assume Math/sqrt [String -> Double])
(assume java.lang.Math/abs [Double -> Double])

(ann hypot [Double Double -> Double])
(ann norm  [Double Double -> Double])
