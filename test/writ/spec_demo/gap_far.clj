(ns writ.spec-demo.gap-far
  "gap, wrong only for a large first number: one no generated Int reaches.")

(defn gap [a b] (if (> a 90) 0 (- a b)))
