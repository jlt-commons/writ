(ns writ.spec-demo.member
  "A club member as a plain map: an id, an email, points, and a nickname
  the member may or may not have set.")

(defn join [id email]
  {:id id :email email :points 0})

(defn award [m n]
  (assoc m :points (+ (:points m) n)))

(defn nickname [m]
  (or (:nick m) (:email m)))
