(ns writ.spec-demo.balance-spec
  "Two laws no lever could satisfy together: one says the result always
  rises above the input, the other that it always falls below it.  Each
  fails on its own; together they name an impossible function."
  (:require [writ.spec :refer [spec ann law]]
            [writ.spec-demo.balance :refer [flip]]))

(spec writ.spec-demo.balance)

(ann flip [Int -> Int])

(law rises (forall [x Int] (> (flip x) x)))
(law falls (forall [x Int] (< (flip x) x)))
