(ns writ.spec-demo.index-user
  "A search from the start, through writ.spec-demo.index's scan."
  (:require [writ.spec-demo.index :as ix]))

(defn find-k
  "Where k first is in xs: [:Take i], or [:None n] when it is not."
  [xs k]
  (ix/scan xs k 0))
