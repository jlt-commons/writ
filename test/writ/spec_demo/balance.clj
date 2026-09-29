(ns writ.spec-demo.balance
  "A lever that moves a weight one either way.")

(defn flip [x]
  (if (neg? x) (inc x) (dec x)))
