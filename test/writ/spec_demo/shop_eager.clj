(ns writ.spec-demo.shop-eager
  "The workflow charging before it looks at the login: it breaks the
  component's :requires."
  (:require [writ.spec-demo.auth :as auth]))

(defn checkout [accounts user password total]
  (let [s (auth/login accounts user password)
        paid (auth/charge s total)]
    (if (auth/authed? s) paid 0)))
