(ns writ.spec-demo.sort-effect
  "Broken: isort prints.")

(defn insert [x xs]
  (cons x xs))

(defn isort [xs]
  (println xs)
  xs)
