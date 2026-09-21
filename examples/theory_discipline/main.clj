(ns theory-discipline.main
  "theory_discipline: the implementation.

  Derived from the parity review against bend's guide and paper/BendTT rather
  than a demo: it exercises the rules that review closed.  Locals carry
  quantities like parameters, and pattern binders do too.  A recursive def is
  marked ^{:writ/descend true}, and every recursive call, recur included, must
  shrink.  A match scrutinee is a parameter or a pattern binder, never a
  computed value, and a parametric type may be matched once instantiated.
  Defs reference earlier defs only."
  (:require [writ.defn :as w]))

;; A parametric box: instantiated at Nat it has kind Data, so a Box value may
;; be reused.  The same rule rejects ^:many over (Box (-> Nat Nat)).
(w/data Box [a] (Box a))

;; A list of nats, for the structural walks.
(w/data NatList Nil (Cons Nat NatList))

;; weakening: `n` is unused, which the quantity lattice allows (0 uses of an
;; affine binder is legal).
(w/defn const0 [n :- Nat] :- Nat 0)

;; a local is affine unless marked: `h` feeds both halves of +, so it is
;; ^:many; `d` is read by the test and by dec.
(w/defn ^{:writ/descend true} pow2 [^:many d :- Nat] :- Nat
  (if (zero? d)
    1
    (let [^:many h (pow2 (dec d))]
      (+ h h))))

;; a nameless fn is checked like any other binder: its parameter is affine,
;; used exactly once.
(w/defn apply-inc [^:many x :- Nat] :- Nat
  ((fn [y] (inc y)) x))

;; unbox a parametric box: the match type is the application (Box Nat), and
;; the scrutinee is a parameter.
(w/defn unbox [b :- (Box Nat)] :- Nat
  (w/match b :- (Box Nat)
    ((Box v) v)))

;; the box may be reused, because (Box Nat) instantiates to kind Data.
(w/defn twice-box [^:many b :- (Box Nat)] :- Nat
  (+ (unbox b) (unbox b)))

;; walk a list: the pattern binder `c` is read twice (by = and by +), so it
;; carries ^:many; the recursion shrinks through `t`, a pattern binder.
(w/defn ^{:writ/descend true} total [xs :- NatList] :- Nat
  (w/match xs :- NatList
    (Nil 0)
    ((Cons ^:many c t) (if (= c 0) (total t) (+ c (total t))))))

;; the same sum by loop/recur: marked like any recursion, and every recur
;; shrinks (`dec m`); the accumulator rides along after the shrinking
;; argument, so it is free.
(w/defn ^{:writ/descend true} sum-to [^:many n :- Nat] :- Nat
  (loop [^:many m n
         ^:many acc 0]
    (if (zero? m)
      acc
      (recur (dec m) (+ acc m)))))

;; defs reference earlier defs only: grand-total calls total and
;; twice-box, both defined above it.  A book takes data apart and never
;; builds it, so the box arrives as a parameter.
(w/defn grand-total [^:many xs :- NatList, ^:many b :- (Box Nat)] :- Nat
  (+ (total xs) (twice-box b)))
