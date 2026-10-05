(ns writ.spec-demo.fee
  "A fee charged past a threshold the laws never reach.")

(defn fee [n]
  (if (> n (* 40 40)) 10 0))

(defn floor-fee [n]
  (max 10 (quot n 100)))
