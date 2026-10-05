(ns writ.spec-demo.fee-spec
  "A spec whose law says what a small order costs and nothing else: the
  code's test on large orders only ever goes one way."
  (:require [writ.spec :refer [spec ann law graph]]))

(spec writ.spec-demo.fee {:test false})

(ann fee [Nat -> Nat])

(graph fees {:states {:n Nat} :edges {:n {[fee] #{:n} [floor-fee] #{:n}}}})

(law a-small-order-is-free (forall [n Nat] (=> (<= n 100) (= 0 (fee n)))))

(ann floor-fee [Nat -> Nat])

(law a-small-order-pays-the-floor (forall [n Nat] (=> (<= n 100) (= 10 (floor-fee n)))))
