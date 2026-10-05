(ns writ.spec-demo.lots
  "The lot to take next: of a sku, live at now, the earliest to expire,
  the lowest id of those.")

(defn next-lot [lots sku now]
  (:id (first (sort-by (juxt :expires :id)
                       (filter #(and (= sku (:sku %)) (pos? (:qty %)) (< now (:expires %)))
                               (vals lots))))))
