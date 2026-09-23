(ns writ.spec-demo.sort-loop
  "Broken: isort recurses on its whole input and never terminates.")

(defn occurrences [x xs]
  (if (seq xs)
    (+ (if (= x (first xs)) 1 0) (occurrences x (rest xs)))
    0))

(defn insert [x xs]
  (cons x xs))

(defn isort [xs]
  (if (seq xs)
    (insert (first xs) (isort xs))
    ()))
