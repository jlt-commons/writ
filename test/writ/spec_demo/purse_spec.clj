(ns writ.spec-demo.purse-spec
  "A step whose fn requires a positive amount, guarded by the purse
  covering it: the step's laws, its refusal among them, are under the
  :requires, so they never call spend with nothing to spend."
  (:require [writ.spec :refer [spec ann law graph refine]]))

(spec writ.spec-demo.purse {:test false})

(refine Purse [p Int] (<= 0 p 1000))

(ann spend [Purse Nat -> Int] {:requires (fn [p amt] (pos? amt))})

(graph wallet {:states {:purse Purse}
               :edges {:purse {[spend Nat] {:to #{:purse} :when (fn [p amt] (and (pos? amt) (<= amt p)))}}}})

(law spending-takes-the-amount
  (forall [p Purse, amt Nat] (=> (and (pos? amt) (<= amt p)) (= (- p amt) (spend p amt)))))
