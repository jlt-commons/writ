(ns writ.spec-demo.twolist-wrong-end
  "dequeue that, moving the back to the front, takes its newest item.")

(defn enqueue [q x] (update q :back conj x))

(defn dequeue [q]
  (cond
    (seq (:front q)) (update q :front #(vec (rest %)))
    (seq (:back q)) {:front (vec (butlast (:back q))) :back []}
    :else q))
