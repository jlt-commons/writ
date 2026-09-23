(ns writ.spec-demo.sort-dedup
  "Broken: insert drops an element equal to the head.")

(defn insert [x xs]
  (if (seq xs)
    (if (< x (first xs))
      (cons x xs)
      (if (= x (first xs))
        xs
        (cons (first xs) (insert x (rest xs)))))
    (list x)))

(defn isort [xs]
  (if (seq xs)
    (insert (first xs) (isort (rest xs)))
    ()))
