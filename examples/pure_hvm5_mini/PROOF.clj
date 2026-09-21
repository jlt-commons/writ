(ns pure-hvm5-mini.PROOF
  "pure_hvm5_mini: the proofs, and the verifier.

  Each proof discharges one law with `refl`.  `verify` reads the implementation
  and the laws from disk and runs the whole book through writ's rule engine."
  (:require [pure-hvm5-mini.main]
            [pure-hvm5-mini.LAWS]
            [writ.defn :as w]
            [writ.book :as book]))

(w/proof opens-add-zero-refl      opens-add-zero      refl)
(w/proof run-len-add-zero-refl    run-len-add-zero    refl)
(w/proof book-depth-add-zero-refl book-depth-add-zero refl)

(defn verify
  "Check the implementation, the laws, and the proofs together.
  Returns {:ok true} or throws a Writ: error."
  []
  (book/check-files
    "pure_hvm5_mini/main.clj"
    "pure_hvm5_mini/LAWS.clj"
    "pure_hvm5_mini/PROOF.clj"))
