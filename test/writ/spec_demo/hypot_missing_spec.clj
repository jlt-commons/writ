(ns writ.spec-demo.hypot-missing-spec
  "An assumed host member that does not exist."
  (:require [writ.spec :refer [spec ann assume]]))

(spec writ.spec-demo.hypot {:require :tested})

(assume Math/sqrt [Double -> Double])
(assume Math/abs [Double -> Double])
(assume Math/cubert [Double -> Double])

(ann hypot [Double Double -> Double])
(ann norm  [Double Double -> Double])
