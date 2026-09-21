(ns pure-par-sort.main
  "pure_par_sort: the leaves of a binary tree of numbers, and the operations
  bend's bitonic sort is proved to preserve.

  Ported from bend's demos/pure_par_sort.  bend's Tree is depth-indexed --
  Tree(0) is a Nat, Tree(1+p) a pair of Tree(p) -- which is a dependent type
  writ has no notion of, so the tree here is the ordinary recursive one.  The
  laws in LAWS.clj are about the same leaf sum bend's mix_leaves/sort_leaves
  preserve.  proofs in PROOF.clj."
  (:require [writ.defn :as w]))

;; A leaf holds a number; a branch pairs two subtrees.
(w/data Tree (Leaf Int) (Node Tree Tree))

;; pick b x y is x when b holds, else y.
(w/defn pick [b :- Bool x :- Int y :- Int] :- Int
  (if b x y))

;; The sum of the leaves.
(w/defn ^{:writ/descend true} sum [t :- Tree] :- Int
  (w/match t :- Tree
    ((Leaf n) n)
    ((Node x y) (+ (sum x) (sum y)))))
