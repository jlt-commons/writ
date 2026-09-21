(ns proof-numerics.LAWS
  "proof_numerics: the laws (the spec).

  Each law is an equality.  `refl` proves it when writ.norm reduces both sides
  to the same normal form: the additive and multiplicative identities, and
  arithmetic on literals.  Kept separate from the implementation.

  bend's own LAWS.bend proves add_comm, add_assoc, mul_comm, mul_dist and
  divmod_ok by induction.  writ's gate proves refl-convertible equalities only,
  so the identities below are what it discharges."
  (:require [writ.defn :as w]))

(w/law add-zero      (forall [n Nat] (= (+ n 0) n)))
(w/law add-zero-left (forall [n Nat] (= (+ 0 n) n)))
(w/law mul-one       (forall [n Nat] (= (* n 1) n)))
(w/law mul-one-left  (forall [n Nat] (= (* 1 n) n)))

;; arithmetic on literals is reduced by writ.norm.
(w/law add-lit   (= (+ 4 5) 9))
(w/law add-assoc (= (+ (+ 1 2) 3) (+ 1 (+ 2 3))))
(w/law inc-dec   (= (inc (dec 7)) 7))
