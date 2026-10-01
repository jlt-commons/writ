(ns writ.spec-demo.bulk-off
  "price with the bulk discount from 6000, not 5000.")

(defn price [qty] (if (< qty 6001) (* 3 qty) (* 2 qty)))
