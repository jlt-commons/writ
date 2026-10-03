(ns writ.spec-demo.sort-loosened-spec
  "The held sort spec, loosened as an agent might to get a check through:
  permutation is gone, and insert's signature returns any list of ints."
  (:require [writ.spec :refer [spec ann law graph refine]]))

(spec writ.spec-demo.sort {:baseline "test/writ/spec_demo/sort_baseline.edn" :test false})

(ann insert [Nat (List Nat) -> (List Int)])
(ann isort  [(List Nat) -> (List Nat)])

(defn ascending? [xs]
  (or (empty? xs) (apply <= xs)))

;; a list goes in, a sorted one comes out
(refine Sorted [xs (List Nat)] (ascending? xs))

(graph sorting
  {:states {:unsorted (List Nat), :sorted Sorted}
   :edges  {:unsorted {[isort] #{:sorted}}
            ;; `_` is where the state goes: (insert x sorted-list)
            :sorted   {[insert Nat _] #{:sorted}}}})

(defn occurrences [x xs]
  (count (filter #(= x %) xs)))

;; the output is in order
(law sorted (forall [xs (List Nat)] (ascending? (isort xs))))

;; and holds exactly the input's elements, duplicates included


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
