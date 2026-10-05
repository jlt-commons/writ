(ns writ.spec-demo.lockout
  "Logging in with a lockout after three wrong passwords.")

(defn login [store user password]
  (let [a (get store user)]
    (cond
      (nil? a) store
      (true? (:locked a)) store
      (= password (:password a)) (assoc store user (assoc a :failures 0))
      :else (let [f (inc (:failures a))]
              (assoc store user (assoc a :failures f :locked (<= 3 f)))))))
