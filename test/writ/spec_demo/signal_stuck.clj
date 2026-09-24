(ns writ.spec-demo.signal-stuck
  "A signal that counts up and then stays put: it never changes colour.
  Every tick keeps a light in its own phase, so each edge's law holds,
  but the graph's steps to the next phase are never taken.")

(def GREEN 30)
(def YELLOW 5)
(def RED 30)

(defn tick [light]
  (let [[phase t] light]
    (case phase
      :Green (if (< t GREEN) [:Green (inc t)] light)
      :Yellow (if (< t YELLOW) [:Yellow (inc t)] light)
      :Red (if (< t RED) [:Red (inc t)] light))))
