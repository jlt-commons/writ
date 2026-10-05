(ns writ.spec-demo.lockout-spec
  "A store of accounts, each a record named by a refinement that only
  names it: the prover reads the store's entries for every input."
  (:require [writ.spec :refer [spec ann law graph refine]]))

(spec writ.spec-demo.lockout {:test false :require :proved})

(refine Account [a {:password String, :failures Nat, :locked Bool}] true)

(ann login [(Map String Account) String String -> (Map String Account)])

(graph accounts {:states {:store (Map String Account)}
                 :edges {:store {[login String String] #{:store}}}})

(law an-unknown-user-changes-nothing
  (forall [s (Map String Account), u String, p String]
    (=> (not (contains? s u)) (= s (login s u p)))))

(law a-locked-account-changes-nothing
  (forall [s (Map String Account), u String, p String]
    (=> (true? (:locked (get s u))) (= s (login s u p)))))

(law the-right-password-clears-the-failures
  (forall [s (Map String Account), u String, a Account]
    (let [s (assoc s u (assoc a :locked false))]
      (=> (some? (get s u))
          (= 0 (:failures (get (login s u (:password a)) u)))))))

(law a-wrong-password-counts
  (forall [s (Map String Account), u String, p String]
    (=> (and (contains? s u) (not (:locked (get s u))) (not= p (:password (get s u))))
        (= (inc (:failures (get s u))) (:failures (get (login s u p) u))))))
