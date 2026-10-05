(ns writ.spec-demo.unwritten-spec
  "A spec whose target is not written yet: it is checked alone. Its law
  and its examples agree."
  (:require [writ.spec :refer [spec ann law graph refine example]]))

(spec writ.spec-demo.unwritten {:test false})

(refine Price [p Nat] (pos? p))

(ann price [Nat -> Nat] {:requires (fn [q] (pos? q))})

(graph pricing {:states {:q Nat :p Price} :edges {:q {[price] #{:p}}}})

(law the-price (forall [q Nat] (=> (pos? q) (= (price q) (* 3 q)))))

(example price [2] 6)
