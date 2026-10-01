(ns writ.spec-demo.bulk-weak-spec
  "The price below 5000 only: nothing says what a bulk order costs."
  (:require [writ.spec :refer [spec ann law graph refine]]))

(spec writ.spec-demo.bulk {:test false})

(refine Bulk [q Nat] (<= 5000 q))

(ann price [Nat -> Nat])

(graph pricing {:states {:bulk Bulk :price Nat} :edges {:bulk {[price] #{:price}}}})

(law the-small-price (forall [q Nat] (=> (< q 5000) (= (price q) (* 3 q)))))
