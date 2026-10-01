(ns writ.spec-demo.spend-spec
  "Accounts are built with room to spare, so no generated spend goes past
  the limit and the law's comparison is never false. writ counts how each
  comparison came out and asks the solver for an input that turns one the
  trials never turned. The law counts flags with frequencies, so the
  prover does not read it; the comparison alone the solver does."
  (:require [writ.spec :refer [spec ann refine graph law]]))

(spec writ.spec-demo.spend {:test false})

(defn roomy [a] (assoc a :limit (+ 1000 (:spent a) (:limit a))))

(refine Account [a {:spent Nat, :limit Nat, :flags (List Keyword)}] (<= (:spent a) (:limit a)) {:build roomy})

(ann may-spend? [Account Nat -> Bool])

(graph till {:states {:account Account, :answer Bool}
             :edges {:account {[may-spend? Nat] #{:answer}}}})

(law spending-stays-within-the-limit
  (forall [a Account, x Nat]
    (= (may-spend? a x)
       (and (<= (+ (:spent a) x) (:limit a)) (not (contains? (frequencies (:flags a)) :frozen))))))
