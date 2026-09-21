(ns proof-insertion-sort.LAWS
  "proof_insertion_sort: the laws (the spec).

  bend's LAWS.bend states sort_sorted (the output ascends) and sort_perm (sort
  permutes its input, by counts).  Both are inductive; writ's gate discharges
  refl-convertible equalities only, so the laws below record the identities it
  proves, over `count`, `sort` and their arguments.  Kept separate from the code."
  (:require [writ.defn :as w]))

(w/law count-add-zero      (= (+ (count x xs) 0) (count x xs)))
(w/law count-add-zero-left (= (+ 0 (count x xs)) (count x xs)))
(w/law count-mul-one        (= (* (count x xs) 1) (count x xs)))
(w/law sort-refl           (= (sort xs) (sort xs)))
