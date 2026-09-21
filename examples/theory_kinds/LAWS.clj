(ns theory-kinds.LAWS
  "theory_kinds: the laws (the spec).

  These go past plain equalities.  bend's BendTT proof surface has hypotheses,
  conjunctions, universals and existentials, and proofs are ordinary
  definitions; writ's gate now reads all of those.  `refl` still discharges a
  convertible equality, and a named law may be cited as a lemma."
  (:require [writ.defn :as w]))

;; A universal: for every n, n + 0 = n.  Proved by a function of n.
(w/law add-zero-all (forall [x Nat] (= (+ x 0) x)))

;; An implication, proved by handing the hypothesis straight back.
(w/law imp-refl (=> (= a b) (= a b)))

;; A conjunction of two convertible equalities.
(w/law both-zero (and (= (+ 0 0) 0) (= (+ 1 0) 1)))

;; An existential, discharged with a witness.
(w/law some-zero (exists [x Nat] (= (+ x 0) x)))

;; A law that leans on another law.
(w/law base-eq (= (+ 2 0) 2))
(w/law cited (and (= (+ 2 0) 2) (= (+ 3 0) 3)))
