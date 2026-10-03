(ns writ.spec-demo.lending-lax
  "may-borrow? with the block itself let through: wrong only at 500.")

(def block 500)

(defn may-borrow? [m] (<= (:fines m) block))
