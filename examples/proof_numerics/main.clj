(ns proof-numerics.main
  "proof_numerics: the implementation.

  Ported from bend's demos/proof_numerics.  The laws live in LAWS.clj and the
  proofs (and the verifier) in PROOF.clj, kept apart from this code."
  (:require [writ.defn :as w]))

;; A list of nats.  length and sum recurse structurally over it.
(w/data NatList Nil (Cons Nat NatList))

;; Primitive recursion on Nat.  `a` and `b` are each reached more than once, so
;; they are marked ^:many (reusable).  An unmarked parameter is affine.
(w/defn ^{:writ/descend true} add [^:many a :- Nat ^:many b :- Nat] :- Nat
  (if (zero? a)
    b
    (inc (add (dec a) b))))

;; mul through add; both `a` and `b` are reached twice.
(w/defn ^{:writ/descend true} mul [^:many a :- Nat ^:many b :- Nat] :- Nat
  (if (zero? a)
    0
    (add b (mul (dec a) b))))

;; ^:writ/descend turns on the structural-descent rule: each recursive call must
;; shrink an argument.  Here `tail` is destructured from `xs` by the match.
(w/defn ^{:writ/descend true} length [xs :- NatList] :- Nat
  (w/match xs :- NatList
    (Nil 0)
    ((Cons _ tail) (inc (length tail)))))

(w/defn ^{:writ/descend true} sum [xs :- NatList] :- Nat
  (w/match xs :- NatList
    (Nil 0)
    ((Cons head tail) (add head (sum tail)))))
