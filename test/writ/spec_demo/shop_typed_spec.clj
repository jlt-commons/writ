(ns writ.spec-demo.shop-typed-spec
  "The workflow's contract naming the component's types: a Session of
  the auth spec, generated here."
  (:require [writ.spec :refer [spec ann law graph]]
            ))

(spec writ.spec-demo.shop {:test false :uses [writ.spec-demo.auth-spec]})

(ann checkout [(Map String String) String String Nat -> Nat])

(graph shopping {:states {:accounts (Map String String) :paid Nat}
                 :edges {:accounts {[checkout String String Nat] #{:paid}}}})

(law a-wrong-password-pays-nothing
  (forall [accounts (Map String String), user String, password String, total Nat]
    (=> (not= password (get accounts user)) (= 0 (checkout accounts user password total)))))

(law a-sessions-user-with-a-wrong-password-pays-nothing
  (forall [s Session, accounts (Map String String), total Nat]
    (=> (not= "nope" (get accounts (:user s))) (= 0 (checkout accounts (:user s) "nope" total)))))
