(ns writ.spec-demo.lots-untied
  "The lot to take next: of a sku, live at now, the earliest to expire,
  -- wrongly -- whichever came first of those.")

(defn next-lot [lots sku now]
  (:id (first (sort-by :expires
                       (filter #(and (= sku (:sku %)) (pos? (:qty %)) (< now (:expires %)))
                               (vals lots))))))
