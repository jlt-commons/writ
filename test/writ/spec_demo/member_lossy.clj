(ns writ.spec-demo.member-lossy
  "join forgets to start the member's points, in a way the static check
  cannot see: only running it shows the key is missing.")

(defn join [id email]
  (zipmap [:id :email] [id email]))

(defn award [m n]
  (assoc m :points (+ (:points m) n)))

(defn nickname [m]
  (or (:nick m) (:email m)))
