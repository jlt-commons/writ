(ns pure-par-sort.PROOF
  "pure_par_sort: the proofs, and the verifier.

  Each proof discharges one law with `refl`.  `verify` reads the implementation
  and the laws from disk and runs the whole book through writ's rule engine."
  (:require [pure-par-sort.main]
            [pure-par-sort.LAWS]
            [writ.defn :as w]
            [writ.book :as book]))

(w/proof sum-add-zero-refl      sum-add-zero      refl)
(w/proof sum-add-zero-left-refl sum-add-zero-left refl)
(w/proof sum-mul-one-refl       sum-mul-one       refl)

(defn verify
  "Check the implementation, the laws, and the proofs together.
  Returns {:ok true} or throws a Writ: error."
  []
  (book/check-files
    "pure_par_sort/main.clj"
    "pure_par_sort/LAWS.clj"
    "pure_par_sort/PROOF.clj"))
