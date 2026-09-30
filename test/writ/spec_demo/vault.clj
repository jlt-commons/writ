(ns writ.spec-demo.vault
  "A vault the owner and clerks pay into, and only the owner closes.")

(defn deposit [v who amt]
  (if (contains? #{:owner :clerk} (:role who))
    [:Open (+ (second v) amt)]
    v))

(defn close [v who]
  (if (= :owner (:role who))
    [:Closed 0]
    v))
