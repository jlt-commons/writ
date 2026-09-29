(ns writ.spec-demo.account
  "An account that pays out what it holds, refuses what it does not,
  and closes.")

(defn withdraw [a amt]
  (if (<= amt (second a)) [:Open (- (second a) amt)] a))

(defn close [a]
  [:Closed 0])
