(ns writ.spec-demo.clip-over
  "take-upto takes one too many.")

(defn take-upto [xs n]
  (take (inc n) xs))

(defn clamp [lo hi x]
  (max lo (min hi x)))

(defn clamp-digit [x]
  (clamp 0 9 x))
