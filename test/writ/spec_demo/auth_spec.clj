(ns writ.spec-demo.auth-spec
  "The component's contract: a login is authenticated exactly when the
  password is the stored one, and only an authenticated session may be
  charged, the amount it is charged."
  (:require [writ.spec :refer [spec ann law graph refine]]))

(spec writ.spec-demo.auth {:test false})

(refine Session [s {:user String, :authed Bool}] true)

(ann login   [(Map String String) String String -> Session])
(ann authed? [Session -> Bool])
(ann charge  [Session Nat -> Nat] {:requires (fn [s amount] (authed? s))})

(graph auth {:states {:creds (Map String String) :session Session :paid Nat}
             :edges {:creds {[login String String] #{:session}}
                     :session {[charge Nat] #{:paid}}}})

(law the-right-password-authenticates
  (forall [accounts (Map String String), user String]
    (=> (contains? accounts user) (authed? (login accounts user (get accounts user))))))

(law a-wrong-password-does-not
  (forall [accounts (Map String String), user String, password String]
    (=> (not= password (get accounts user)) (not (authed? (login accounts user password))))))

(law a-charge-is-the-amount
  (forall [s Session, amount Nat] (=> (authed? s) (= amount (charge s amount)))))
