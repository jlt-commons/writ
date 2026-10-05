(ns writ.spec-demo.auth
  "A component: logging in against stored passwords, and charging an
  authenticated session.")

(defn login [accounts user password]
  {:user user :authed (= password (get accounts user))})

(defn authed? [session]
  (:authed session))

(defn charge [session amount]
  amount)
