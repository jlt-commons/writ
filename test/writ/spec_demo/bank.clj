(ns writ.spec-demo.bank
  "Withdrawing from an open account: paid out when the balance covers it,
  and otherwise the account is overdrawn and charged a fee.")

(defn withdraw [a amt]
  (cond
    (not= :open (:status a)) a
    (<= amt (:balance a)) (assoc a :balance (- (:balance a) amt))
    :else (assoc a :status :overdrawn :fee 10)))
