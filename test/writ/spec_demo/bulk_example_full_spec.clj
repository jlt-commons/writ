(ns writ.spec-demo.bulk-example-full-spec
  "The full bulk spec with the same example: the laws say what a bulk
  order costs, so they pin price down at the example too."
  (:require [writ.spec :refer [spec ann law graph refine example]]))

(spec writ.spec-demo.bulk {:test false})

(refine Bulk [q Nat] (<= 5000 q))

(ann price [Nat -> Nat])

(graph pricing {:states {:bulk Bulk :price Nat} :edges {:bulk {[price] #{:price}}}})

(law the-price (forall [q Nat] (= (price q) (if (< q 5000) (* 3 q) (* 2 q)))))

(example price [6000] 12000)
(example price [10] 30)
