(ns writ.spec-demo.bulk-example-named-spec
  "The full bulk spec, its example's argument and result named by the
  spec's own values: the stand-in off the example is off at what they
  are, so the laws pin price down there as they do at a literal."
  (:require [writ.spec :refer [spec ann law graph refine example]]))

(spec writ.spec-demo.bulk {:test false})

(refine Bulk [q Nat] (<= 5000 q))

(ann price [Nat -> Nat])

(graph pricing {:states {:bulk Bulk :price Nat} :edges {:bulk {[price] #{:price}}}})

(law the-price (forall [q Nat] (= (price q) (if (< q 5000) (* 3 q) (* 2 q)))))

(def big-order 6000)
(def big-price 12000)

(example price [big-order] big-price)

;; a bound the law asserts: true wherever the law holds, so its coming out
;; one way only is no sign of an input the trials missed
(law never-dearer-than-retail (forall [q Nat] (<= (price q) (* 3 q))))

;; an example's argument may call the target itself
(example price [(quot (price big-order) 2)] big-price)
