(ns writ.spec-demo.sort-identity
  "Broken: well typed and total, but sorts nothing.")

(defn occurrences [x xs]
  (if (seq xs)
    (+ (if (= x (first xs)) 1 0) (occurrences x (rest xs)))
    0))

(defn insert [x xs]
  (cons x xs))

(defn isort [xs]
  xs)
