(ns writ.spec-demo.sort-missing
  "Broken: insert is gone.")

(defn occurrences [x xs]
  (if (seq xs)
    (+ (if (= x (first xs)) 1 0) (occurrences x (rest xs)))
    0))

(defn isort [xs]
  xs)
