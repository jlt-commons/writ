(ns writ.spec-demo.parity
  "A count that steps by one, then is wrapped.")

(defn bump [n] (inc n))

(defn wrap [n] [:Up n])
