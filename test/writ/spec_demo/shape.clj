(ns writ.spec-demo.shape
  "Shapes, and their area.")

(defn area [s]
  (case (first s)
    :circle (* 3 (second s) (second s))
    :square (* (second s) (second s))))
