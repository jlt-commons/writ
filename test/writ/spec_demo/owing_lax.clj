(ns writ.spec-demo.owing-lax
  "may-borrow? with the block itself let through.")

(defn may-borrow? [fines fees tags]
  (and (<= (+ fines (* 2 fees)) 500) (not (contains? (frequencies tags) :banned))))
