(ns writ.spec-demo.spend
  "May an account spend an amount: only within its limit, and not while
  it is frozen.")

(defn may-spend? [a x]
  (and (<= (+ (:spent a) x) (:limit a)) (not (contains? (frequencies (:flags a)) :frozen))))
