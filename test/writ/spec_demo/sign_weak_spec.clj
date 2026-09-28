(ns writ.spec-demo.sign-weak-spec
  "sign's laws for positive and negative n, and none for 0: every stand-in
  of the usual kinds fails them, but a sign that is wrong at 0 passes."
  (:require [writ.spec :refer [spec ann law graph]]))

(spec writ.spec-demo.sign)

(ann sign [Int -> Int])

(graph signs {:states {:n Int} :edges {}})

(law a-positive-is-1 (forall [n Nat] (= 1 (sign (inc n)))))
(law a-negative-is-minus-1 (forall [n Nat] (= -1 (sign (- -1 n)))))
(law sign-example (= -1 (sign -3)))
