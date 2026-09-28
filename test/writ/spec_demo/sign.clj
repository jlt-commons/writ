(ns writ.spec-demo.sign
  "The sign of an integer.")

(defn sign
  "1 for a positive n, -1 for a negative one, 0 for 0."
  [n]
  (cond (pos? n) 1
        (neg? n) -1
        :else 0))
