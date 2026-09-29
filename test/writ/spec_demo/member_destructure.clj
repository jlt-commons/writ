(ns writ.spec-demo.member-destructure
  "The member fns, reading keys by destructuring.")

(defn join [id email]
  {:id id :email email :points 0})

(defn award [m n]
  (let [{:keys [points]} m]
    (assoc m :points (+ points n))))

(defn nickname [{:keys [nick email]}]
  (or nick email))
