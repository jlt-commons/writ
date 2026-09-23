(ns writ.spec-demo.sort-spec
  "The contract for writ.spec-demo.sort: signatures for the public API and
  the laws its behaviour must satisfy."
  (:require [writ.spec :refer [spec ann law]]))

(spec writ.spec-demo.sort)

(ann occurrences [Nat (List Nat) -> Nat])
(ann insert      [Nat (List Nat) -> (List Nat)])
(ann isort       [(List Nat) -> (List Nat)])

(defn ascending? [xs]
  (or (empty? xs) (apply <= xs)))

;; decided statically: writ.norm proves it for every n
(law add-zero (forall [n Nat] (= (+ n 0) n)))

;; closed: decided by running the code once
(law insert-empty (= (insert 3 ()) (list 3)))

;; universal: checked against generated inputs
(law sorted      (forall [xs (List Nat)] (ascending? (isort xs))))
(law permutation (forall [x Nat, xs (List Nat)]
                   (= (occurrences x (isort xs)) (occurrences x xs))))
(law smallest-first
  (forall [xs (List Nat)]
    (=> (seq xs) (= (first (isort xs)) (apply min xs)))))
(law has-fixed-point (exists [xs (List Nat)] (= (isort xs) xs)))
