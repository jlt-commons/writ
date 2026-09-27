(ns writ.spec-demo.sort-extra
  "The insertion sort with a public fn the spec never planned.")

(defn insert [x xs]
  (if (seq xs)
    (if (<= x (first xs))
      (cons x xs)
      (cons (first xs) (insert x (rest xs))))
    (list x)))

(defn isort [xs]
  (if (seq xs)
    (insert (first xs) (isort (rest xs)))
    ()))

(defn largest [xs] (last (isort xs)))
