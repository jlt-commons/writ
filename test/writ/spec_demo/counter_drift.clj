(ns writ.spec-demo.counter-drift
  "Like counter, but at one high count -- a multiple of five a sample
  of the band rarely reaches -- it drifts off the band.  The climb from
  the start walks straight into it.")

(defn step [c]
  (let [[band n] c]
    (case band
      :Low  (if (< n 4) [:Low (inc n)] [:High 10])
      :High (if (= n 95) [:High 96] [:High (+ n 5)]))))
