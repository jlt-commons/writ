(ns writ.spec-demo.till
  "A till the owner and clerks pay into, a hundred at most at a time.")

(defn pay-in [t who amt]
  (if (and (contains? #{:owner :clerk} (:role who)) (pos? amt) (<= amt 100))
    [:Open (+ (second t) amt)]
    t))
