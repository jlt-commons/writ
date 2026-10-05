(ns writ.spec-demo.tags
  "A pipeline over positions: each item tagged with its index.")

(defn tag [xs]
  (let [n (count xs)]
    (mapv (fn [i] (assoc (nth xs i) :k i)) (range n))))
