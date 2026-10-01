(ns writ.spec-demo.twolist
  "A queue kept as two vectors: taken from the front, added at the back,
  and the back moved to the front when the front runs out.")

(defn enqueue [q x] (update q :back conj x))

(defn dequeue [q]
  (cond
    (seq (:front q)) (update q :front #(vec (rest %)))
    (seq (:back q)) {:front (vec (rest (:back q))) :back []}
    :else q))
