(ns pure-par-sum.main
  "pure_par_sum: the fork/join tree of the 2^d numbers from i, and the
  sequential reference it is proved equal to.

  Ported from bend's demos/pure_par_sum.  bend runs `sum` on the GPU or on
  every core; writ has no runtime parallelism, so this is the sequential
  program Bend proves the tree against.  The laws are in LAWS.clj, the proofs
  in PROOF.clj."
  (:require [writ.defn :as w]))

;; 2^d, doubling at each level.  `d` is read by the test and by `dec`, and the
;; local `h` feeds both halves of `+`, so both are reusable rather than affine.
(w/defn ^{:writ/descend true} pow2 [^:many d :- Nat] :- Nat
  (if (zero? d)
    1
    (let [^:many h (pow2 (dec d))]
      (+ h h))))

;; The tree of depth d from i: a leaf is i, otherwise the two halves meet at
;; i + 2^(d-1).  `i` is read in both halves, so it is reusable.
(w/defn ^{:writ/descend true} sum [^:many d :- Nat ^:many i :- Nat] :- Nat
  (if (zero? d)
    i
    (let [^:many p (dec d)
          left (sum p i)
          right (sum p (+ (pow2 p) i))]
      (+ left right))))

;; The sequential loop the tree is proved equal to: it adds i, i+1, .. i+m-1.
(w/defn ^{:writ/descend true} seq [^:many n :- Nat ^:many i :- Nat] :- Nat
  (if (zero? n)
    0
    (let [^:many m (dec n)]
      (+ (seq m i) (+ m i)))))
