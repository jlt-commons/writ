(ns writ.spec-demo.jobs-by-id
  "Jobs by id; the next one is the due :ready job of the highest priority,
  then -- wrongly -- the lowest id before the earliest ready time.")

(defn- due? [j now] (and (= :ready (:status j)) (<= (:ready-at j) now)))

(defn next-job [q now]
  (let [due (filter #(due? % now) (vals (:jobs q)))]
    (when (seq due)
      (:id (first (sort-by (fn [j] [(- (:priority j)) (:id j) (:ready-at j)]) due))))))
