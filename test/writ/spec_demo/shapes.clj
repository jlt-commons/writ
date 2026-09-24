(ns writ.spec-demo.shapes
  "Plain code for testing symbolic evaluation: tagged data with fields,
  destructuring with defaults, a branch that throws, and division.")

(defn perimeter [shape]
  (case (first shape)
    :Square (let [[_ s] shape] (* 4 s))
    :Rect (let [[_ w h] shape] (* 2 (+ w h)))
    :Dot 0))

(defn area [shape]
  (case (first shape)
    :Square (let [[_ s] shape] (* s s))
    :Rect (let [[_ w h] shape] (* w h))
    :Dot 0))

(defn grow [shape]
  (let [[tag a b] shape]
    (case tag
      :Square [:Square (inc a)]
      :Rect [:Rect (inc a) (max b (quot a 2))]
      :Dot [:Square 1])))

(defn bucket [n]
  (cond (neg? n) [:low (abs n)]
        (< n 10) [:mid (mod n 3)]
        :else [:high (quot n 10)]))

(defn pick [xs i]
  (nth xs i :none))
