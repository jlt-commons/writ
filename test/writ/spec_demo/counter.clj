(ns writ.spec-demo.counter
  "A counter that fills a low band one at a time, then climbs a high
  band five at a time without end.")

(defn step [c]
  (let [[band n] c]
    (case band
      :Low  (if (< n 4) [:Low (inc n)] [:High 10])
      :High [:High (+ n 5)])))
