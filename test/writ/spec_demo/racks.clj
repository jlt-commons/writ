(ns writ.spec-demo.racks
  "Three slots, each holding at most one item, and a queue of people per slot.")

(defn put [r slot n]
  (if (contains? (:items r) slot)
    r
    (assoc-in r [:items slot] {:slot slot :n n})))
