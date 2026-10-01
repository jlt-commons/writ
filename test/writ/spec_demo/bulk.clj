(ns writ.spec-demo.bulk
  "Unit prices: 3 each, 2 each from 5000 up.")

(defn price [qty] (if (< qty 5000) (* 3 qty) (* 2 qty)))
