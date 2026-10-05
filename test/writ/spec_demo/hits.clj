(ns writ.spec-demo.hits
  "A component: a counter of hits that never goes below zero.")

(defn add-hits [h n]
  (assoc h :count (+ (:count h) n)))
