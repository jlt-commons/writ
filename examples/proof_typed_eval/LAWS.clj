(ns proof-typed-eval.LAWS
  "proof_typed_eval: the laws (the spec).

  The evaluator's result is a Nat; the laws record that adding zero to it, on
  either side, changes nothing.  writ.norm discharges these by the additive
  identity, whatever `(eval e)` reduces to.  Kept separate from the code."
  (:require [writ.defn :as w]))

(w/law add-zero-right (= (+ (eval e) 0) (eval e)))
(w/law add-zero-left  (= (+ 0 (eval e)) (eval e)))
(w/law eval-refl      (forall [e Expr] (= (eval e) (eval e))))
