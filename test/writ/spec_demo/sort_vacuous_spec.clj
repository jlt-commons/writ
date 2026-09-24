(ns writ.spec-demo.sort-vacuous-spec
  "A spec whose laws are true of any implementation."
  (:require [writ.spec :refer [spec ann law graph]]))

(spec writ.spec-demo.sort)

(ann insert [Nat (List Nat) -> (List Nat)])
(ann isort  [(List Nat) -> (List Nat)])

(graph sorting
  {:states {:item Nat, :unsorted (List Nat), :sorted (List Nat)}
   :edges  {:unsorted {[isort] #{:sorted}}
            :item     {[insert (List Nat)] #{:sorted}}}})

;; restates itself: true whatever isort does
(law sort-refl (forall [xs (List Nat)] (= (isort xs) (isort xs))))

;; about arithmetic, not about the sort
(law add-zero (forall [n Nat] (= (+ n 0) n)))

;; about the input, not about the sort
(law count-self (forall [xs (List Nat)] (= (count xs) (count xs))))

(law sorted (forall [xs (List Nat)] (apply <= 0 (isort xs))))
