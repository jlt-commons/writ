(ns writ.spec-demo.light
  "A traffic light kept in a tuple with how long it has shown. Broken:
  `tick` has no clause for Amber.")

(defn tick [state]
  (let [[light n] state]
    (case (first light)
      :Red (if (< n 3) [light (inc n)] [[:Green] 0])
      :Green (if (< n 3) [light (inc n)] [[:Amber] 0]))))
