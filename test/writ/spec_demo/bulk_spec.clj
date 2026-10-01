(ns writ.spec-demo.bulk-spec
  "The price, every case of it. 5000 is past any generated Nat, so a
  mutant that moves the threshold is told apart only at 5000 itself."
  (:require [writ.spec :refer [spec ann law graph refine]]))

(spec writ.spec-demo.bulk {:test false})

(refine Bulk [q Nat] (<= 5000 q))

(ann price [Nat -> Nat])

(graph pricing {:states {:bulk Bulk :price Nat} :edges {:bulk {[price] #{:price}}}})

(law the-price (forall [q Nat] (= (price q) (if (< q 5000) (* 3 q) (* 2 q)))))
