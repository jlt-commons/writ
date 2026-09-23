(ns writ.spec-demo.signal-skip
  "signal, but yellow gives way to green: the light skips red.")

(def GREEN 30)
(def YELLOW 5)
(def RED 30)

(defn tick [light]
  (let [[phase t] light]
    (case phase
      :Green (if (< t GREEN) [:Green (inc t)] [:Yellow 0])
      :Yellow (if (< t YELLOW) [:Yellow (inc t)] [:Green 0])
      :Red (if (< t RED) [:Red (inc t)] [:Green 0]))))
