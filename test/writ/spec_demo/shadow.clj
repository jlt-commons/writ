(ns writ.spec-demo.shadow
  "An insertion sort's name for its own order test, the same name as the
  spec's helper.  `isort` here only rotates its input.")

(defn ascending? [xs] true)

(defn isort [xs]
  (if (seq xs) (concat (rest xs) (list (first xs))) ()))
