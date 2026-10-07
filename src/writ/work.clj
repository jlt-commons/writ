(ns writ.work
  "One law's search measured in steps, not time.  The rewriter, the solver
  and symbolic evaluation spend from the same allowance, so a search stops
  at the same place on every machine, and a proof found once is found
  again.")

(def ^:dynamic *left*
  "When bound, a volatile of the steps a search has left; unbound, there
  is no limit."
  nil)

(defn spend!
  "Spend n steps: true once the allowance is gone."
  [n]
  (when-let [l *left*] (neg? (vswap! l - n))))

(defn spent?
  "Is the allowance gone?"
  []
  (when-let [l *left*] (neg? @l)))

(defn allowance
  "A fresh allowance of n steps, to bind *left* to; nil for no limit."
  [n]
  (when n (volatile! n)))
