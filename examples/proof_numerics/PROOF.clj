(ns proof-numerics.PROOF
  "proof_numerics: the proofs, and the verifier.

  Each proof discharges one law with `refl`.  `verify` reads the implementation
  and the laws from disk and runs the whole book through writ's rule engine, so
  the written code is checked against the spec that sits beside it."
  (:require [proof-numerics.main]
            [proof-numerics.LAWS]
            [writ.defn :as w]
            [writ.book :as book]))

(w/proof add-zero-refl      add-zero      (fn [n] refl))
(w/proof add-zero-left-refl add-zero-left (fn [n] refl))
(w/proof mul-one-refl       mul-one       (fn [n] refl))
(w/proof mul-one-left-refl  mul-one-left  (fn [n] refl))
(w/proof add-lit-refl       add-lit       refl)
(w/proof add-assoc-refl     add-assoc     refl)
(w/proof inc-dec-refl       inc-dec       refl)

(defn verify
  "Check the implementation, the laws, and the proofs together.
  Returns {:ok true} or throws a Writ: error."
  []
  (book/check-files
    "proof_numerics/main.clj"
    "proof_numerics/LAWS.clj"
    "proof_numerics/PROOF.clj"))
