(ns writ.spec-demo.bulk-example-spec
  "The weak bulk spec, with an example at a bulk quantity: the example
  holds, but no law says what a bulk order costs, so a fn that agrees
  everywhere but there passes every law, and the report says so."
  (:require [writ.spec :refer [spec ann law graph refine example]]))

(spec writ.spec-demo.bulk {:test false})

(refine Bulk [q Nat] (<= 5000 q))

(ann price [Nat -> Nat])

(graph pricing {:states {:bulk Bulk :price Nat} :edges {:bulk {[price] #{:price}}}})

(law the-small-price (forall [q Nat] (=> (< q 5000) (= (price q) (* 3 q)))))

(example price [6000] 12000)
