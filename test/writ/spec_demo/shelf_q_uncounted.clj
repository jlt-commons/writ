(ns writ.spec-demo.shelf-q-uncounted
  "lend that forgets to count the loan.")

(defn lend [lib m c]
  (if (and (contains? (:members lib) m) (= :shelf (get-in lib [:copies c :status])))
    (-> lib
        (assoc-in [:copies c :status] :loaned)
        (assoc-in [:copies c :holder] m))
    lib))
