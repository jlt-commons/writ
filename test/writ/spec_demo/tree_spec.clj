(ns writ.spec-demo.tree-spec
  "The contract for writ.spec-demo.tree, a binary search tree of nats.

  The problem: a set of nats that keeps its elements in order. The central
  law says exactly that -- a tree built by inserting xs lists the distinct
  elements of xs in ascending order -- against clojure.core as the model."
  (:require [writ.spec :refer [spec data ann law]]))

(spec writ.spec-demo.tree)

(data Tree Leaf (Node Tree Nat Tree))

(ann size    [Tree -> Nat])
(ann to-list [Tree -> (List Nat)])
(ann insert  [Nat Tree -> Tree])

(defn strictly-ascending? [xs]
  (or (empty? xs) (apply < xs)))

;; the meaning of the tree: the set of what went in, in order
(law holds-a-sorted-set
  (forall [xs (List Nat)]
    (= (to-list (reduce (fn [acc v] (insert v acc)) [:Leaf] xs))
       (sort (distinct xs)))))

(law size-counts (forall [t Tree] (= (size t) (count (to-list t)))))

(law insert-adds (forall [x Nat, t Tree] (some #{x} (to-list (insert x t)))))

(law insert-keeps-order
  (forall [x Nat, t Tree]
    (=> (strictly-ascending? (to-list t))
        (strictly-ascending? (to-list (insert x t))))))

(law insert-into-empty (= (insert 1 [:Leaf]) [:Node [:Leaf] 1 [:Leaf]]))
