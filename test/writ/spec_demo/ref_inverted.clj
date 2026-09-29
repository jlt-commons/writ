(ns writ.spec-demo.ref-inverted
  "keep-where keeps what the predicate rejects.")

(defn at [v i]
  (nth v i))

(defn keep-where [p xs]
  (remove p xs))
