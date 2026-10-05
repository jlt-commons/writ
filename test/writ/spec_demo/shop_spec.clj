(ns writ.spec-demo.shop-spec
  "The workflow's contract, built on the auth component's: what it pays
  follows from the component's proved laws, without its code."
  (:require [writ.spec :refer [spec ann law graph]]))

(spec writ.spec-demo.shop {:test false :uses [writ.spec-demo.auth-spec]})

(ann checkout [(Map String String) String String Nat -> Nat])

(graph shopping {:states {:accounts (Map String String) :paid Nat}
                 :edges {:accounts {[checkout String String Nat] #{:paid}}}})

(law the-right-password-pays-the-total
  (forall [accounts (Map String String), user String, total Nat]
    (=> (contains? accounts user) (= total (checkout accounts user (get accounts user) total)))))

(law a-wrong-password-pays-nothing
  (forall [accounts (Map String String), user String, password String, total Nat]
    (=> (not= password (get accounts user)) (= 0 (checkout accounts user password total)))))
