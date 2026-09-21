(ns proof-insertion-sort.PROOF
  "proof_insertion_sort: the proofs, and the verifier.

  Each proof discharges one law with `refl`.  `verify` reads the implementation
  and the laws from disk and runs the whole book through writ's rule engine."
  (:require [proof-insertion-sort.main]
            [proof-insertion-sort.LAWS]
            [writ.defn :as w]
            [writ.book :as book]))

(w/proof count-add-zero-refl  count-add-zero  refl)
(w/proof count-add-zero-left-refl count-add-zero-left refl)
(w/proof count-mul-one-refl   count-mul-one   refl)
(w/proof sort-refl-proof      sort-refl       refl)

(defn verify
  "Check the implementation, the laws, and the proofs together.
  Returns {:ok true} or throws a Writ: error."
  []
  (book/check-files
    "proof_insertion_sort/main.clj"
    "proof_insertion_sort/LAWS.clj"
    "proof_insertion_sort/PROOF.clj"))
