(ns writ.spec-demo.total-spec
  (:require [writ.spec :refer [spec ann law graph]]))

(spec writ.spec-demo.total)

(ann total           [(List Nat) -> Nat])
(ann size            [(List Nat) -> Nat])
(ann total-by-reduce [(List Nat) -> Nat])

(graph summing
  {:states {:items (List Nat), :sum Nat, :count Nat}
   :edges  {:items {[total] #{:sum}, [total-by-reduce] #{:sum}, [size] #{:count}}}})

(law total-of-two (forall [a Nat, b Nat] (= (+ a b) (total (list a b)))))
(law total-sums (forall [xs (List Nat)] (= (total xs) (apply + xs))))
(law size-counts (forall [xs (List Nat)] (= (size xs) (count xs))))
(law reduce-sums (forall [xs (List Nat)] (= (total-by-reduce xs) (apply + xs))))
(law reduce-appends
  (forall [xs (List Nat), ys (List Nat)]
    (= (total-by-reduce (concat xs ys)) (+ (total-by-reduce xs) (total-by-reduce ys)))))
