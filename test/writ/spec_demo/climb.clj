(ns writ.spec-demo.climb
  "A counter that climbs two at a time.")

(defn climb [c]
  (let [[tag n] c]
    [tag (+ n 2)]))
