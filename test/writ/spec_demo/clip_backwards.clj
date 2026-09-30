(ns writ.spec-demo.clip-backwards
  "clamp-digit hands clamp its bounds the wrong way round.")

(defn take-upto [xs n]
  (take n xs))

(defn clamp [lo hi x]
  (max lo (min hi x)))

(defn clamp-digit [x]
  (clamp 9 0 x))
