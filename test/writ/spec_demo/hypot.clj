(ns writ.spec-demo.hypot
  "The length of a vector, through Math/sqrt, a host member writ does not
  check.")

(defn hypot [x y]
  (Math/sqrt (+ (* x x) (* y y))))

(defn norm [x y]
  (java.lang.Math/abs (hypot x y)))
