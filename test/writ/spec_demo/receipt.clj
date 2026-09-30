(ns writ.spec-demo.receipt
  "A receipt that keeps its total with its items.")

(defn add-item [r price]
  (assoc r :items (conj (:items r) price) :total (+ (:total r) price)))
