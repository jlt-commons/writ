(ns writ.spec-demo.shelf
  "A shelf that fills a slot at a time, and is done.")

(defn fill [s]
  (let [[phase n] s]
    (case phase
      :Open (if (< n 2) [:Open (inc n)] [:Done 0])
      :Done [:Done 0])))
