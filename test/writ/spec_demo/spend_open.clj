(ns writ.spec-demo.spend-open
  "may-spend? that forgot the limit.")

(defn may-spend? [a x]
  (and (>= x 0) (not (contains? (frequencies (:flags a)) :frozen))))
