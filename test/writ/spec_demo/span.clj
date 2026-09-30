(ns writ.spec-demo.span
  "Whether two half-open spans [start, end) share a unit.")

(defn overlaps? [a b]
  (< (max (:start a) (:start b)) (min (:end a) (:end b))))
