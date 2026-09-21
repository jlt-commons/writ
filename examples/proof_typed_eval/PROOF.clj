(ns proof-typed-eval.PROOF
  "proof_typed_eval: the proofs, and the verifier.

  Each proof discharges one law with `refl`.  `verify` reads the implementation
  and the laws from disk and runs the whole book through writ's rule engine."
  (:require [proof-typed-eval.main]
            [proof-typed-eval.LAWS]
            [writ.defn :as w]
            [writ.book :as book]))

(w/proof add-zero-right-refl add-zero-right refl)
(w/proof add-zero-left-refl  add-zero-left  refl)
(w/proof eval-refl-proof     eval-refl      (fn [e] refl))

(defn verify
  "Check the implementation, the laws, and the proofs together.
  Returns {:ok true} or throws a Writ: error."
  []
  (book/check-files
    "proof_typed_eval/main.clj"
    "proof_typed_eval/LAWS.clj"
    "proof_typed_eval/PROOF.clj"))
