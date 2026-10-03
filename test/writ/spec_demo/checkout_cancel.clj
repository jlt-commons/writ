(ns writ.spec-demo.checkout-cancel
  "An order paid only with its exact total, then shipped, or cancelled
  before it ships.")

(defn pay [o amt]
  (if (and (= :placed (first o)) (= amt (second o))) [:paid (second o)] o))

(defn ship [o]
  (if (= :paid (first o)) [:shipped (second o)] o))

(defn cancel [o]
  (if (contains? #{:placed :paid} (first o)) [:cancelled (second o)] o))
