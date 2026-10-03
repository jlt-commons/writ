(ns writ.spec-demo.shelf-q
  "A lending desk: copies on loan to members, who count their loans.")

(defn lend [lib m c]
  (if (and (contains? (:members lib) m) (= :shelf (get-in lib [:copies c :status])))
    (-> lib
        (assoc-in [:copies c :status] :loaned)
        (assoc-in [:copies c :holder] m)
        (update-in [:members m :loans] inc))
    lib))
