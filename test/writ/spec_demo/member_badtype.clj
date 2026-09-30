(ns writ.spec-demo.member-badtype
  "join starts the points as a string.")

(defn join [id email]
  {:id id :email email :points "0"})

(defn award [m n]
  (assoc m :points (+ (:points m) n)))

(defn nickname [m]
  (or (:nick m) (:email m)))
