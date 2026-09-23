(ns writ.spec-demo.tree-spec
  "The contract for writ.spec-demo.tree."
  (:require [writ.spec :refer [spec data ann law]]))

(spec writ.spec-demo.tree)

(data Tree Leaf (Node Tree Nat Tree))

(ann size    [Tree -> Nat])
(ann to-list [Tree -> (List Nat)])
(ann insert  [Nat Tree -> Tree])

(defn strictly-ascending? [xs]
  (or (empty? xs) (apply < xs)))

(law size-counts (forall [t Tree] (= (size t) (count (to-list t)))))

(law insert-adds (forall [x Nat, t Tree] (some #{x} (to-list (insert x t)))))

(law insert-keeps-order
  (forall [x Nat, t Tree]
    (=> (strictly-ascending? (to-list t))
        (strictly-ascending? (to-list (insert x t))))))

(law insert-into-empty (= (insert 1 [:Leaf]) [:Node [:Leaf] 1 [:Leaf]]))
