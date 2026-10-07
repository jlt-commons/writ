(ns writ.spec-demo.roster
  "Children by id, in start order: where one is.")

(defn index-of
  "The position of the first of ids equal to id, or nil when none is."
  [ids id]
  (when (seq ids)
    (if (= id (first ids))
      0
      (when-let [i (index-of (rest ids) id)] (inc i)))))
