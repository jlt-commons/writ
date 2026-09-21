(ns theory-kinds.main
  "theory_kinds: the implementation.

  Derived from paper/BendTT rather than a demo: it exercises the kind rule that
  makes reuse sound.  A binder may be marked ^:many (reusable) only when its
  type has kind Data, so a datatype of plain fields may be reused while a
  function type may not.  Also shows the product types -- (Tuple ..), (List ..)
  and the multi-value return (& ..)."
  (:require [writ.defn :as w]))

;; Pair has kind Data: both fields are nats, so a Pair value may be reusable.
(w/data Pair (Pair Nat Nat))

;; A recursive tree; Nil and Node are both Data.
(w/data Tree Nil (Node Nat Tree Tree))

(w/defn fst-p [p :- Pair] :- Nat
  (w/match p :- Pair
    ((Pair a b) a)))

(w/defn snd-p [p :- Pair] :- Nat
  (w/match p :- Pair
    ((Pair a b) b)))

;; p is reached twice, so it is marked ^:many.  That is allowed because Pair is
;; Data; the same rule rejects ^:many over a function type.
(w/defn pair-sum [^:many p :- Pair] :- Nat
  (+ (fst-p p) (snd-p p)))

;; Product and list types are well-kinded in annotations.
(w/defn tuple-id [t :- (Tuple Nat Nat)] :- (Tuple Nat Nat) t)
(w/defn list-id  [xs :- (List Nat)] :- (List Nat) xs)

;; A multi-value return is the n-ary product (& ..).
(w/defn pair-up [^:many x :- Nat] :- (& Nat Nat) (cons x x))
