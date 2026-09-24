(ns writ.spec-demo.flow-spec
  "A graph whose states are plain compound types: data flow only."
  (:require [writ.spec :refer [spec ann law graph]]))

(spec writ.spec-demo.sort)

(ann insert [Nat (List Nat) -> (List Nat)])
(ann isort  [(List Nat) -> (List Nat)])

(graph sorting
  {:states {:unsorted (List Nat), :sorted (List Nat)}
   :edges  {:unsorted {[isort] #{:sorted}}}})

(defn occurrences [x xs] (count (filter #(= x %) xs)))
(defn ascending? [xs] (or (empty? xs) (apply <= xs)))

(law sorted (forall [xs (List Nat)] (ascending? (isort xs))))
(law permutation (forall [x Nat, xs (List Nat)] (= (occurrences x (isort xs)) (occurrences x xs))))
(law insert-keeps-sorted (forall [x Nat, xs (List Nat)] (=> (ascending? xs) (ascending? (insert x xs)))))
(law insert-adds (forall [x Nat, xs (List Nat)] (= (occurrences x (insert x xs)) (inc (occurrences x xs)))))
