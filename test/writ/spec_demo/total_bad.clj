(ns writ.spec-demo.total-bad
  "Broken: size counts every element twice, total skips the first, and the
  reduce keeps the largest instead of the sum.")

(defn total [xs]
  (loop [xs (rest xs), acc 0]
    (if (seq xs)
      (recur (rest xs) (+ acc (first xs)))
      acc)))

(defn size [xs]
  (loop [xs xs, n 0]
    (if (seq xs) (recur (rest xs) (+ n 2)) n)))

(defn total-by-reduce [xs]
  (reduce (fn [acc x] (max acc x)) 0 xs))
