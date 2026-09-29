(ns writ.spec-demo.tally
  "How many times each value comes up.")

(defn tally [xs]
  (frequencies xs))
