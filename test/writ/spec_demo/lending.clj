(ns writ.spec-demo.lending
  "Who may borrow: a member owing less than the block.")

(def block 500)

(defn may-borrow? [m] (< (:fines m) block))
