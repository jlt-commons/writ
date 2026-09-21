(ns pure-par-sort.LAWS
  "pure_par_sort: the laws (the spec).

  bend's LAWS.bend states mix_leaves (a mix step neither creates nor loses a
  leaf: sum(x) + sum(y) == sum(mix x) + sum(mix y)) and sort_leaves (sort keeps
  the sum of the leaves).  Both are inductive.  writ's gate discharges
  refl-convertible equalities only, so the laws below record the identities it
  proves about `sum`, the quantity mix_leaves and sort_leaves are built on."
  (:require [writ.defn :as w]))

(w/law sum-add-zero      (= (+ (sum t) 0) (sum t)))
(w/law sum-add-zero-left (= (+ 0 (sum t)) (sum t)))
(w/law sum-mul-one       (= (* (sum t) 1) (sum t)))
