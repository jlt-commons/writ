(ns writ.spec-demo.paint
  "Paint for a shape, through its area."
  (:require [writ.spec-demo.shape :as shape]))

(defn tins [s]
  (case (first s)
    :circle (inc (shape/area s))
    :square (shape/area s)))
