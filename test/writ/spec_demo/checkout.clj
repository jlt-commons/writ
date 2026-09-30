(ns writ.spec-demo.checkout
  "An order paid only with its exact total, then shipped.")

(defn pay [o amt]
  (if (and (= :placed (first o)) (= amt (second o))) [:paid (second o)] o))

(defn ship [o]
  (if (= :paid (first o)) [:shipped (second o)] o))
