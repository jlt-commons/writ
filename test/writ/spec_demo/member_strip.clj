(ns writ.spec-demo.member-strip
  "join builds a member and takes every key back out.")

(defn join [id email]
  (dissoc {:id id :email email :points 0} :id :email :points))

(defn award [m n]
  (assoc m :points (+ (:points m) n)))

(defn nickname [m]
  (or (:nick m) (:email m)))
