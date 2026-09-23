(ns writ.spec-demo.sort-count
  "Broken: isort returns a number, not a list.")

(defn insert [x xs]
  (cons x xs))

(defn isort [xs]
  (count xs))
