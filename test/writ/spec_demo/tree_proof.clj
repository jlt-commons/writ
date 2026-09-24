(ns writ.spec-demo.tree-proof
  "How writ.spec-demo.tree-spec's holds-a-sorted-set is proved.

  The prover models (sort (distinct xs)) as a fold inserting each element
  into a sorted list: the elements below it, it, the elements above it.
  Building the tree is the same kind of fold, inserting into a tree, so
  the law follows from one fact about insert -- listing a search tree
  after an insert is that list insert -- and the fold lemma it gives."
  (:require [writ.spec :refer [proof-of lemma hint]]
            [writ.spec-demo.tree :refer [to-list insert]]))

(proof-of writ.spec-demo.tree-spec)

;; a search tree: everything left of a value is below it, everything right
;; of it above
(defn bst? [t]
  (case (first t)
    :Leaf true
    :Node (let [[_ l v r] t]
            (and (bst? l) (bst? r)
                 (every? #(< % v) (to-list l))
                 (every? #(> % v) (to-list r))))))

;; inserting a value below (above) every element keeps them all below (above)
(lemma below-insert
  (forall [x Nat, v Nat, t Tree]
    (=> (and (every? #(< % v) (to-list t)) (< x v))
        (every? #(< % v) (to-list (insert x t))))))

(lemma above-insert
  (forall [x Nat, v Nat, t Tree]
    (=> (and (every? #(> % v) (to-list t)) (> x v))
        (every? #(> % v) (to-list (insert x t))))))

(lemma insert-keeps-bst
  (forall [x Nat, t Tree] (=> (bst? t) (bst? (insert x t)))))

;; what a bound on a list says about the part of it below or above x;
;; (concat xs) is xs as a seq, () for nil, as filter gives
(lemma none-below
  (forall [x Nat, v Nat, xs (List Nat)]
    (=> (and (every? #(> % v) xs) (<= x v)) (= (filter #(< % x) xs) ()))))

(lemma all-above
  (forall [x Nat, v Nat, xs (List Nat)]
    (=> (and (every? #(> % v) xs) (<= x v)) (= (filter #(> % x) xs) (concat xs)))))

(lemma all-below
  (forall [x Nat, v Nat, xs (List Nat)]
    (=> (and (every? #(< % v) xs) (>= x v)) (= (filter #(< % x) xs) (concat xs)))))

(lemma none-above
  (forall [x Nat, v Nat, xs (List Nat)]
    (=> (and (every? #(< % v) xs) (>= x v)) (= (filter #(> % x) xs) ()))))

;; listing a search tree after an insert is inserting into its list
(lemma to-list-insert
  (forall [x Nat, t Tree]
    (=> (bst? t)
        (= (to-list (insert x t))
           (concat (filter #(< % x) (to-list t)) [x] (filter #(> % x) (to-list t)))))))

;; building the tree from any search tree is the fold of that list insert
(lemma build-lists
  (forall [xs (List Nat), acc Tree]
    (=> (bst? acc)
        (= (to-list (reduce (fn [acc v] (insert v acc)) acc xs))
           (reduce (fn [s x] (concat (filter #(< % x) s) [x] (filter #(> % x) s)))
                   (to-list acc) xs)))))

(hint below-insert {:induct t})
(hint above-insert {:induct t})
(hint insert-keeps-bst {:induct t :use [below-insert above-insert]})
(hint none-below {:induct xs})
(hint all-above {:induct xs})
(hint all-below {:induct xs})
(hint none-above {:induct xs})
(hint to-list-insert {:induct t :use [none-below all-above all-below none-above]})
(hint build-lists {:induct xs :vary [acc] :use [insert-keeps-bst to-list-insert]})
(hint holds-a-sorted-set {:use [build-lists]})
