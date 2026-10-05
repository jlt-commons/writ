(ns writ.spec-demo.numbered
  "Each element numbered by its place.")

(defn number-items [xs]
  (vec (map-indexed (fn [i x] {:i i :x x}) xs)))
