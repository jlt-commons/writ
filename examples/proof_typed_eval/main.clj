(ns proof-typed-eval.main
  "proof_typed_eval: a small typed expression language and its evaluator.

  Ported from bend's demos/proof_typed_eval.  The laws live in LAWS.clj and the
  proofs in PROOF.clj."
  (:require [writ.defn :as w]))

(w/data Expr
  (ELit Int)
  (EAdd Expr Expr))

;; Structural descent: each recursive call shrinks `e` by destructuring it.
(w/defn ^{:writ/descend true} eval [e :- Expr] :- Int
  (w/match e :- Expr
    ((ELit n) n)
    ((EAdd l r) (+ (eval l) (eval r)))))
