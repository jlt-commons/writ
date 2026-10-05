(ns writ.spec-demo.fold
  "A fold whose step conjes onto an accumulator the prover cannot tell is
  a vector.")

(defn- step [c r] [(+ c r) r])

(defn run-all [c rs]
  (reduce (fn [[c placed] r]
            (let [[c' x] (step c r)]
              [c' (conj placed x)]))
          [c []]
          rs))
