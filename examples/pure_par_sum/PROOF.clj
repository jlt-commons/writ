(ns pure-par-sum.PROOF
  "pure_par_sum: the proofs, and the verifier.

  Each proof discharges one law with `refl`.  `verify` reads the implementation
  and the laws from disk and runs the whole book through writ's rule engine."
  (:require [pure-par-sum.main]
            [pure-par-sum.LAWS]
            [writ.defn :as w]
            [writ.book :as book]))

(w/proof sum-add-zero-refl      sum-add-zero      refl)
(w/proof sum-add-zero-left-refl sum-add-zero-left refl)
(w/proof seq-add-zero-refl      seq-add-zero      refl)

(defn verify
  "Check the implementation, the laws, and the proofs together.
  Returns {:ok true} or throws a Writ: error."
  []
  (book/check-files
    "pure_par_sum/main.clj"
    "pure_par_sum/LAWS.clj"
    "pure_par_sum/PROOF.clj"))
