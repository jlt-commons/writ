(ns writ.spec-demo.spend-freq-spec
  "The law with a clause that always holds, read through frequencies,
  which neither the prover nor the solver reads: the trials never see it
  false, the solver finds no input that makes it so, and the report says
  so."
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
       (and (<= 0 (count (frequencies (:flags a))))
            (<= (+ (:spent a) x) (:limit a))
            (not (contains? (frequencies (:flags a)) :frozen))))))
