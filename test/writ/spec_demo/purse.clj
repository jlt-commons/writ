(ns writ.spec-demo.purse
  "Spending from a purse: a positive amount, never more than it holds.")

(defn spend [p amt]
  (if (<= amt p) (- p amt) p))
