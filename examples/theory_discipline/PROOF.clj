(ns theory-discipline.PROOF
  "theory_discipline: the proofs, and the verifier.

  refl discharges a convertible equality.  A law may be cited by name, but
  only after its own proof: arith-chain cites arith-five, proved above.
  `verify` reads the implementation, the laws and the proofs from disk and
  runs the whole book through every rule."
  (:require [theory-discipline.main]
            [theory-discipline.LAWS]
            [writ.defn :as w]
            [writ.book :as book]))

(w/proof arith-five-p arith-five refl)

(w/proof arith-chain-p arith-chain (pair arith-five refl))

(defn verify
  "Check the implementation, the laws, and the proofs together.
  Returns {:ok true} or throws a Writ: error."
  []
  (book/check-files
    "theory_discipline/main.clj"
    "theory_discipline/LAWS.clj"
    "theory_discipline/PROOF.clj"))
