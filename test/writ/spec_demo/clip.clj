(ns writ.spec-demo.clip
  "Taking at most n, and clamping into a range.")

(defn take-upto [xs n]
  (take n xs))

(defn clamp [lo hi x]
  (max lo (min hi x)))

(defn clamp-digit [x]
  (clamp 0 9 x))
