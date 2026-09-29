(ns writ.spec-demo.gauge-bad
  "Like gauge, but cools three at a time, so an even count can come out
  odd -- a landing that breaks the hot state's invariant.")

(defn cool [g]
  (let [[phase n] g]
    (case phase
      :Hot  (if (>= n 3) [:Hot (- n 3)] [:Cold 0])
      :Cold [:Cold 0])))
