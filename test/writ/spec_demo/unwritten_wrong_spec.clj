(ns writ.spec-demo.unwritten-wrong-spec
  "The unwritten target's spec with an example its law contradicts, one
  that breaks the fn's :requires, and a law that calls no fn of it: each
  is found before any code is written."
  (:require [writ.spec :refer [spec ann law graph refine example]]))

(spec writ.spec-demo.unwritten {:test false})

(refine Price [p Nat] (pos? p))

(ann price [Nat -> Nat] {:requires (fn [q] (pos? q))})

(graph pricing {:states {:q Nat :p Price} :edges {:q {[price] #{:p}}}})

(law the-price (forall [q Nat] (=> (pos? q) (= (price q) (* 3 q)))))

(law arithmetic (forall [q Nat] (= (* 3 q) (+ q q q))))

(example price [2] 7)
(example price [0] 0)
