(ns writ.spec-demo.sort
  "Insertion sort over a list of nats. Plain Clojure: writ is never
  mentioned here; the contract lives in writ.spec-demo.sort-spec.")

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
