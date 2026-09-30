(ns writ.spec-demo.member-typo
  "award reads a key the record does not have.")

(defn join [id email]
  {:id id :email email :points 0})

(defn award [m n]
  (assoc m :points (+ (or (:point m) 0) n)))

(defn nickname [m]
  (or (:nick m) (:email m)))
