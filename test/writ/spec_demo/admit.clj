(ns writ.spec-demo.admit
  "Admission: an adult member is let in.")

(defn admit [age member]
  (if (and (<= 18 age) member) :in :out))
