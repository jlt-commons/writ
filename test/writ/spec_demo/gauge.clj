(ns writ.spec-demo.gauge
  "A gauge that cools while it runs hot, an even count at a time, and
  settles when its count runs out.")

(defn cool [g]
  (let [[phase n] g]
    (case phase
      :Hot  (if (odd? n) [:Hot (dec n)] (if (>= n 2) [:Hot (- n 2)] [:Cold 0]))
      :Cold [:Cold 0])))
