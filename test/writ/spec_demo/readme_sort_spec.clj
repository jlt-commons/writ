(ns writ.spec-demo.readme-sort-spec
  "The README's sort spec, word for word but for the target: the graph's
  edges carry `sorted` and `insert-keeps-sorted`, and both are proved."
  (:require [writ.spec :refer [spec ann law graph refine]]))

(spec writ.spec-demo.sort {:require :proved})

(ann insert      [Nat (List Nat) -> (List Nat)])
(ann isort       [(List Nat) -> (List Nat)])

(defn ascending? [xs]
  (or (empty? xs) (apply <= xs)))

;; what makes a list sorted
(refine Sorted [xs (List Nat)] (ascending? xs))

;; the problem's states: a list goes in, a sorted list comes out, and
;; inserting into a sorted list keeps it sorted (`_` is where the state goes)
(graph sorting
  {:states {:unsorted (List Nat), :sorted Sorted}
   :edges  {:unsorted {[isort] #{:sorted}}
            :sorted   {[insert Nat _] #{:sorted}}}})

(defn occurrences [x xs]
  (count (filter #(= x %) xs)))

;; the graph already says a sort puts its input in order; it also
;; keeps every element, duplicates included
(law permutation (forall [x Nat, xs (List Nat)]
                   (= (occurrences x (isort xs)) (occurrences x xs))))

;; and insert adds exactly one x
(law insert-adds (forall [x Nat, xs (List Nat)]
                   (= (occurrences x (insert x xs)) (inc (occurrences x xs)))))
