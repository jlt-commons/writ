(ns writ.spec-demo.sort-pairs
  "The insertion sort, with fn literals and a defn that destructure their
  parameters.")

(defn- head-and-rest [[x & more]]
  [x more])

(defn insert [x xs]
  (if (seq xs)
    (let [[h t] (head-and-rest xs)]
      (if (<= x h)
        (cons x xs)
        (cons h (insert x (rest xs)))))
    (list x)))

(defn isort [xs]
  (reduce (fn [acc [i v]] (if (< i 0) acc (insert v acc)))
          ()
          (map-indexed vector xs)))
