(ns writ.spec-demo.member-local
  "award through a local fn, whose return the static check cannot see.")

(defn join [id email]
  {:id id :email email :points 0})

(defn award [m n]
  (let [f (fn [x] (assoc x :points (+ (:points x) n)))]
    (f m)))

(defn nickname [m]
  (or (:nick m) (:email m)))
