(ns pure-par-sum.LAWS
  "pure_par_sum: the laws (the spec).

  bend's LAW is tree_is_seq: for any d and i, sum(d, i) == seq(2^d, i) -- the
  tree adds the same numbers as the loop.  bend's PROOF.bend proves it by
  induction on the depth.  writ's gate discharges refl-convertible equalities
  only, so the laws below record the identities it proves over the two
  accumulators; tree_is_seq itself is stated in the docstring and is the reason
  the two functions sit here together."
  (:require [writ.defn :as w]))

(w/law sum-add-zero      (= (+ (sum d i) 0) (sum d i)))
(w/law sum-add-zero-left (= (+ 0 (sum d i)) (sum d i)))
(w/law seq-add-zero      (= (+ (seq n i) 0) (seq n i)))
