(ns writ.spec-demo.shop
  "A workflow on the auth component: log in, and pay only when the login
  holds."
  (:require [writ.spec-demo.auth :as auth]))

(defn checkout [accounts user password total]
  (let [s (auth/login accounts user password)]
    (if (auth/authed? s) (auth/charge s total) 0)))
