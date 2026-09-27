(ns writ.spec-demo.sort-lemma-spec
  "The sort's contract, demanding proof, without the lemma about insert
  that the proof of `sorted` needs: that lemma is the prover's business,
  kept in writ.spec-demo.sort-lemma-proof."
  (:require [writ.spec :refer [spec ann law graph refine]]))

(spec writ.spec-demo.sort {:require :proved})

(ann insert [Nat (List Nat) -> (List Nat)])
(ann isort  [(List Nat) -> (List Nat)])

(defn ascending? [xs] (or (empty? xs) (apply <= xs)))

;; no edge for insert: what it keeps is the proof namespace's lemma
(refine Sorted [xs (List Nat)] (ascending? xs))

(graph sorting
  {:states {:unsorted (List Nat), :sorted Sorted}
   :edges  {:unsorted {[isort] #{:sorted}}}})
(defn occurrences [x xs] (count (filter #(= x %) xs)))

(law sorted (forall [xs (List Nat)] (ascending? (isort xs))))
(law permutation (forall [x Nat, xs (List Nat)] (= (occurrences x (isort xs)) (occurrences x xs))))
(law insert-adds (forall [x Nat, xs (List Nat)] (= (occurrences x (insert x xs)) (inc (occurrences x xs)))))
