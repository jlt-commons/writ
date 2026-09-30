(ns writ.spec-demo.member-nil
  "nickname hands back the nickname, which may be absent.")

(defn join [id email]
  {:id id :email email :points 0})

(defn award [m n]
  (assoc m :points (+ (:points m) n)))

(defn nickname [m]
  (:nick m))
