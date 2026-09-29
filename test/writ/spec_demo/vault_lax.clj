(ns writ.spec-demo.vault-lax
  "close lets a clerk close the vault.")

(defn deposit [v who amt]
  (if (contains? #{:owner :clerk} (:role who))
    [:Open (+ (second v) amt)]
    v))

(defn close [v who]
  (if (contains? #{:owner :clerk} (:role who))
    [:Closed 0]
    v))
