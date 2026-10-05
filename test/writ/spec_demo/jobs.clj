(ns writ.spec-demo.jobs
  "Jobs by id; the next one is the due :ready job of the highest priority,
  then the earliest ready time, then the lowest id.")

(defn- due? [j now] (and (= :ready (:status j)) (<= (:ready-at j) now)))

(defn next-job [q now]
  (let [due (filter #(due? % now) (vals (:jobs q)))]
    (when (seq due)
      (:id (first (sort-by (fn [j] [(- (:priority j)) (:ready-at j) (:id j)]) due))))))
