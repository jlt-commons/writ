(ns theory-kinds.PROOF
  "theory_kinds: the proofs, and the verifier.

  A universal is proved by `(fn [x] ..)`, an implication by `(fn [h] ..)` that
  reuses the hypothesis, a conjunction by `(pair ..)`, and an existential by
  `(witness t pf)`.  A law may be cited by name as a lemma.  `verify` reads the
  implementation, the laws and the proofs from disk and runs the whole book."
  (:require [theory-kinds.main]
            [theory-kinds.LAWS]
            [writ.defn :as w]
            [writ.book :as book]))

(w/proof add-zero-all-p add-zero-all (fn [x] refl))
(w/proof imp-refl-p imp-refl (fn [h] h))
(w/proof both-zero-p both-zero (pair refl refl))
(w/proof some-zero-p some-zero (witness 5 refl))
(w/proof base-eq-p base-eq refl)
(w/proof cited-p cited (pair base-eq refl))

(defn verify
  "Check the implementation, the laws, and the proofs together.
  Returns {:ok true} or throws a Writ: error."
  []
  (book/check-files
    "theory_kinds/main.clj"
    "theory_kinds/LAWS.clj"
    "theory_kinds/PROOF.clj"))
