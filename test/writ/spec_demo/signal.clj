(ns writ.spec-demo.signal
  "A traffic signal: a phase and how many ticks it has been showing. Each
  phase shows for a fixed number of ticks, then gives way to the next.")

(def GREEN 30)
(def YELLOW 5)
(def RED 30)

(defn tick [light]
  (let [[phase t] light]
    (case phase
      :Green (if (< t GREEN) [:Green (inc t)] [:Yellow 0])
      :Yellow (if (< t YELLOW) [:Yellow (inc t)] [:Red 0])
      :Red (if (< t RED) [:Red (inc t)] [:Green 0]))))
