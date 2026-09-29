(ns writ.spec-demo.ref-lenient
  "at answers nil past the end instead of throwing.")

(defn at [v i]
  (get v i))

(defn keep-where [p xs]
  (filter p xs))
