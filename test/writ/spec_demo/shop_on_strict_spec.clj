(ns writ.spec-demo.shop-on-strict-spec
  "The workflow built on a component that fails its own spec."
  (:require [writ.spec :refer [spec ann law graph]]))

(spec writ.spec-demo.shop {:test false :uses [writ.spec-demo.auth-strict-spec]})

(ann checkout [(Map String String) String String Nat -> Nat])

(graph shopping {:states {:accounts (Map String String) :paid Nat}
                 :edges {:accounts {[checkout String String Nat] #{:paid}}}})

(law a-wrong-password-pays-nothing
  (forall [accounts (Map String String), user String, password String, total Nat]
    (=> (not= password (get accounts user)) (= 0 (checkout accounts user password total)))))
