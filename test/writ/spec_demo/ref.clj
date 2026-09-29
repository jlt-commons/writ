(ns writ.spec-demo.ref
  "Reading a vector by index, and keeping what a predicate picks.")

(defn at [v i]
  (nth v i))

(defn keep-where [p xs]
  (filter p xs))
