(ns writ.spec-demo.sort-spec
  "The contract for writ.spec-demo.sort, an insertion sort over nats.

  The problem: put a list of nats in ascending order, keeping every
  element. The laws say that and nothing about how it is done, and they
  measure the result with the spec's own vocabulary (`ascending?`,
  `occurrences`), never with the implementation's."
  (:require [writ.spec :refer [spec ann law]]))

(spec writ.spec-demo.sort)

(ann insert [Nat (List Nat) -> (List Nat)])
(ann isort  [(List Nat) -> (List Nat)])

(defn ascending? [xs]
  (or (empty? xs) (apply <= xs)))

(defn occurrences [x xs]
  (count (filter #(= x %) xs)))

;; the output is in order
(law sorted (forall [xs (List Nat)] (ascending? (isort xs))))

;; and holds exactly the input's elements, duplicates included
(law permutation (forall [x Nat, xs (List Nat)]
                   (= (occurrences x (isort xs)) (occurrences x xs))))

;; insert is the step: it keeps an ordered list ordered, and adds x
(law insert-keeps-sorted
  (forall [x Nat, xs (List Nat)]
    (=> (ascending? xs) (ascending? (insert x xs)))))
(law insert-adds (forall [x Nat, xs (List Nat)]
                   (= (occurrences x (insert x xs)) (inc (occurrences x xs)))))
(law insert-empty (= (insert 3 ()) (list 3)))

(law smallest-first
  (forall [xs (List Nat)]
    (=> (seq xs) (= (first (isort xs)) (apply min xs)))))
(law has-fixed-point (exists [xs (List Nat)] (= (isort xs) xs)))
