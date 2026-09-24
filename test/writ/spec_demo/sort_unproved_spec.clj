(ns writ.spec-demo.sort-unproved-spec
  "The sort's contract at the default level, with one law that demands
  proof the prover cannot give."
  (:require [writ.spec :refer [spec ann law graph]]))

(spec writ.spec-demo.sort)

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

(law smallest-first
  {:require :proved}
  (forall [xs (List Nat)]
    (=> (seq xs) (= (first (isort xs)) (apply min xs)))))
