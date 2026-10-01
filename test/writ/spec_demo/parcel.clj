(ns writ.spec-demo.parcel
  "A parcel is placed, paid for in full, then shipped.")

(defn pay [o amt]
  (if (and (= :placed (:status o)) (= amt (:total o)))
    (assoc o :status :paid :paid amt)
    o))
