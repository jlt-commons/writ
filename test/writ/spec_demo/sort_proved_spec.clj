(ns writ.spec-demo.sort-proved-spec
  "The sort's contract, demanding proof: every law must be proved, not
  only tested, unless it says why it cannot be yet."
  (:require [writ.spec :refer [spec ann law graph]]))

(spec writ.spec-demo.sort {:require :proved})

(ann insert [Nat (List Nat) -> (List Nat)])
(ann isort  [(List Nat) -> (List Nat)])

(graph sorting
  {:states {:item Nat, :unsorted (List Nat), :sorted (List Nat)}
   :edges  {:unsorted {[isort] #{:sorted}}
            :item     {[insert (List Nat)] #{:sorted}}}})

(defn ascending? [xs]
  (or (empty? xs) (apply <= xs)))

(defn occurrences [x xs]
  (count (filter #(= x %) xs)))

(law sorted (forall [xs (List Nat)] (ascending? (isort xs))))
(law permutation (forall [x Nat, xs (List Nat)]
                   (= (occurrences x (isort xs)) (occurrences x xs))))
(law insert-keeps-sorted
  (forall [x Nat, xs (List Nat)]
    (=> (ascending? xs) (ascending? (insert x xs)))))
(law insert-adds (forall [x Nat, xs (List Nat)]
                   (= (occurrences x (insert x xs)) (inc (occurrences x xs)))))
(law insert-empty (= (insert 3 ()) (list 3)))

(law smallest-first
  {:require :tested :because "the prover has no model of min over a list yet"}
  (forall [xs (List Nat)]
    (=> (seq xs) (= (first (isort xs)) (apply min xs)))))

(law has-fixed-point (exists [xs (List Nat)] (= (isort xs) xs)))
