(ns writ.spec-demo.member-rename
  "award also rewrites the member's email.")

(defn join [id email]
  {:id id :email email :points 0})

(defn award [m n]
  (assoc m :points (+ (:points m) n) :email (str (:email m) "!")))

(defn nickname [m]
  (or (:nick m) (:email m)))
