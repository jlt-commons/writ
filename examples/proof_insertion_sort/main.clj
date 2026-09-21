(ns proof-insertion-sort.main
  "proof_insertion_sort: insertion sort on a list of Nat.

  Ported from bend's demos/proof_insertion_sort.  bend carries its proof of
  sortedness inside the comparison verdict; writ states the sort's properties as
  laws in LAWS.clj and proves what its rule engine checks: exhaustive matches,
  structural descent, and the affine/many quantities.

  Lists are tagged vectors, read by writ's constructor patterns: `:Nil`, or
  `[:Cons head tail]`."
  (:require [writ.defn :as w]))

;; A list of nats.
(w/data NatList Nil (Cons Nat NatList))

;; n plus one when b holds.
(w/defn bump [b :- Bool n :- Nat] :- Nat
  (if b (inc n) n))

;; how many times x occurs in xs.  `x` is reached twice, so it is ^:many.
(w/defn ^{:writ/descend true} count [^:many x :- Nat xs :- NatList] :- Nat
  (w/match xs :- NatList
    (Nil 0)
    ((Cons h t) (bump (= x h) (count x t)))))

;; insert x into xs, keeping xs ascending.  `x` and `h` are each reached
;; twice (the comparison, and the rebuilt cell), so both are ^:many.
(w/defn ^{:writ/descend true} insert [^:many x :- Nat xs :- NatList] :- NatList
  (w/match xs :- NatList
    (Nil [:Cons x :Nil])
    ((Cons ^:many h t)
     (if (<= x h)
       [:Cons x [:Cons h t]]
       [:Cons h (insert x t)]))))

;; insertion sort: insert the head into the sorted tail.
(w/defn ^{:writ/descend true} sort [xs :- NatList] :- NatList
  (w/match xs :- NatList
    (Nil :Nil)
    ((Cons h t) (insert h (sort t)))))
