(ns writ.spec-demo.total
  "Sums and counts written as loops with accumulators, and as a reduce.")

(defn total [xs]
  (loop [xs xs, acc 0]
    (if (seq xs)
      (recur (rest xs) (+ acc (first xs)))
      acc)))

(defn size [xs]
  (loop [xs xs, n 0]
    (if (seq xs) (recur (rest xs) (inc n)) n)))

(defn total-by-reduce [xs]
  (reduce (fn [acc x] (+ acc x)) 0 xs))
