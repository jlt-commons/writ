(ns writ.spec-demo.sort-desc
  "Broken: the comparison is flipped, so the output descends.")

(defn insert [x xs]
  (if (seq xs)
    (if (>= x (first xs))
      (cons x xs)
      (cons (first xs) (insert x (rest xs))))
    (list x)))

(defn isort [xs]
  (if (seq xs)
    (insert (first xs) (isort (rest xs)))
    ()))
