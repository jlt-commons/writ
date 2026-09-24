(ns writ.spec-demo.signal-throw
  "signal, but a yellow light that has run its time looks past the end of
  a vector: tick throws there.")

(def GREEN 30)
(def YELLOW 5)
(def RED 30)

(defn tick [light]
  (let [[phase t] light]
    (case phase
      :Green (if (< t GREEN) [:Green (inc t)] [:Yellow 0])
      :Yellow (if (< t YELLOW) [:Yellow (inc t)] (nth [[:Red 0]] (- t YELLOW -1)))
      :Red (if (< t RED) [:Red (inc t)] [:Green 0]))))
