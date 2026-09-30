(ns writ.spec-demo.registry-dup
  "register forgets to check the email.")

(defn taken? [db m]
  (or (contains? db (:id m))
      (boolean (some #(= (:email m) (:email %)) (vals db)))))

(defn register [db m]
  (if (contains? db (:id m)) db (assoc db (:id m) m)))
