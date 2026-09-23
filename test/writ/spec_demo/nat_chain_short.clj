(ns writ.spec-demo.nat-chain-short
  "Broken: the guard proves n is at least 2, and the call subtracts 3.")

(defn half [n] 0)
(defn parity [n] 0)
(defn half-by-two [n] 0)

(defn thirds [n]
  (if (>= n 2) (inc (thirds (- n 3))) 0))
