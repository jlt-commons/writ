(ns writ.spec-demo.member-partial
  "join builds a member without its points.")

(defn join [id email]
  {:id id :email email})

(defn award [m n]
  (assoc m :points (+ (:points m) n)))

(defn nickname [m]
  (or (:nick m) (:email m)))
