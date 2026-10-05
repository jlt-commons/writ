(ns writ.spec-demo.auth-strict-spec
  "The component held to a law it breaks: a charge takes a fee. A spec
  built on it builds on a component that fails its own check."
  (:require [writ.spec :refer [spec ann law graph refine]]))

(spec writ.spec-demo.auth {:test false})

(refine Session [s {:user String, :authed Bool}] true)

(ann login   [(Map String String) String String -> Session])
(ann authed? [Session -> Bool])
(ann charge  [Session Nat -> Nat] {:requires (fn [s amount] (authed? s))})

(graph auth {:states {:creds (Map String String) :session Session :paid Nat}
             :edges {:creds {[login String String] #{:session}}
                     :session {[charge Nat] #{:paid}}}})

(law a-charge-takes-a-fee
  (forall [s Session, amount Nat] (=> (authed? s) (= (inc amount) (charge s amount)))))
