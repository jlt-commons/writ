(ns writ.spec-demo.sort-identity
  "Broken: well typed and total, but sorts nothing.")

(defn insert [x xs]
  (cons x xs))

(defn isort [xs]
  xs)
