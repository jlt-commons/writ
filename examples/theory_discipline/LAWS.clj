(ns theory-discipline.LAWS
  "theory_discipline: the laws (the spec).

  The gate reads the book in order: a law may be cited only by a proof that
  comes after its own proof, so citations cannot cycle, a proof is never
  itself a citable law, and a law name is declared once."
  (:require [writ.defn :as w]))

(w/law arith-five (= (+ 2 3) 5))

;; proved second, so its proof may cite arith-five as a lemma.
(w/law arith-chain (and (= (+ 2 3) 5) (= (* 2 2) 4)))
