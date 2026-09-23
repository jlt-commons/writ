(ns writ.spec-demo.sort-loop
  "Broken: isort recurses on its whole input and never terminates.")

(defn insert [x xs]
  (cons x xs))

(defn isort [xs]
  (if (seq xs)
    (insert (first xs) (isort xs))
    ()))
