(ns writ.spec-demo.sign-spec
  "sign, every case of it."
  (:require [writ.spec :refer [spec ann law graph]]))

(spec writ.spec-demo.sign)

(ann sign [Int -> Int])

(graph signs {:states {:n Int} :edges {}})

(law a-positive-is-1 (forall [n Nat] (= 1 (sign (inc n)))))
(law a-negative-is-minus-1 (forall [n Nat] (= -1 (sign (- -1 n)))))
(law sign-example (= -1 (sign -3)))
(law zero-is-0 (= 0 (sign 0)))
