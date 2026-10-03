(ns writ.spec-demo.bank-greedy
  "withdraw that charges the fee on every withdrawal.")

(defn withdraw [a amt]
  (cond
    (not= :open (:status a)) a
    (<= amt (:balance a)) (assoc a :balance (- (:balance a) amt) :fee 10)
    :else (assoc a :status :overdrawn :fee 10)))
