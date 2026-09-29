(ns writ.spec-demo.member-big
  "award resets a member with more than a thousand points: no generated
  member has that many.")

(defn join [id email]
  {:id id :email email :points 0})

(defn award [m n]
  (if (> (:points m) 1000)
    (assoc m :points 0)
    (assoc m :points (+ (:points m) n))))

(defn nickname [m]
  (or (:nick m) (:email m)))
