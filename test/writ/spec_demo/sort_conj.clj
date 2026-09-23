(ns writ.spec-demo.sort-conj
  "Broken: insert puts x in front with conj, which only prepends to a list.")

(defn insert [x xs]
  (if (seq xs)
    (if (<= x (first xs))
      (conj xs x)
      (cons (first xs) (insert x (rest xs))))
    (list x)))

(defn isort [xs]
  (if (seq xs)
    (insert (first xs) (isort (rest xs)))
    ()))
