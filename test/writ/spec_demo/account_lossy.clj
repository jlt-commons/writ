(ns writ.spec-demo.account-lossy
  "Like account, but a refused withdrawal empties the account instead of
  leaving it as it was.")

(defn withdraw [a amt]
  (if (<= amt (second a)) [:Open (- (second a) amt)] [:Open 0]))

(defn close [a]
  [:Closed 0])
