(ns writ.spec-demo.owing
  "Who may borrow, when fees count double against the block.")

(defn may-borrow? [fines fees tags]
  (and (< (+ fines (* 2 fees)) 500) (not (contains? (frequencies tags) :banned))))
