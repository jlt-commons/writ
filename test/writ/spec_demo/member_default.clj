(ns writ.spec-demo.member-default
  "nickname reads the nickname with a default, which a nil nickname
  still gets past.")

(defn join [id email]
  {:id id :email email :points 0})

(defn award [m n]
  (assoc m :points (+ (:points m) n)))

(defn nickname [m]
  (:nick m ""))
