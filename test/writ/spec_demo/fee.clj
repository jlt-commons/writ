(ns writ.spec-demo.fee
  "A fee charged past a threshold the laws never reach.")

(defn fee [n]
  (if (> n (* 40 40)) 10 0))
