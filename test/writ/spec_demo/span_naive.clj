(ns writ.spec-demo.span-naive
  "The textbook test, wrong when a span is empty or backwards: [1, 1)
  holds no unit, yet it is said to overlap [0, 2).")

(defn overlaps? [a b]
  (and (< (:start a) (:end b)) (< (:start b) (:end a))))
