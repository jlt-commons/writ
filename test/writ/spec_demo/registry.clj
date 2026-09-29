(ns writ.spec-demo.registry
  "Members kept by id, no two with the same email.")

(defn taken? [db m]
  (or (contains? db (:id m))
      (boolean (some #(= (:email m) (:email %)) (vals db)))))

(defn register [db m]
  (if (taken? db m) db (assoc db (:id m) m)))
