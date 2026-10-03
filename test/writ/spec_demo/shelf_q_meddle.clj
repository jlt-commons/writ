(ns writ.spec-demo.shelf-q-meddle
  "lend that also marks every copy seen: no rule of the library breaks,
  but it touches copies the loan has nothing to do with.")

(defn lend [lib m c]
  (if (and (contains? (:members lib) m) (= :shelf (get-in lib [:copies c :status])))
    (-> lib
        (assoc-in [:copies c :status] :loaned)
        (assoc-in [:copies c :holder] m)
        (update-in [:members m :loans] inc)
        (update :copies (fn [cs] (into {} (for [[k x] cs] [k (assoc x :seen true)])))))
    lib))
