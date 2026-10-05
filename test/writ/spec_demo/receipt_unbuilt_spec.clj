(ns writ.spec-demo.receipt-unbuilt-spec
  "The receipt without a :build, of three items or more: its values are
  filtered for, and starve."
  (:require [writ.spec :refer [spec ann refine graph law]]))

(spec writ.spec-demo.receipt {:test false})

(refine Receipt [r {:items (Vec Nat), :total Nat}]
  (and (<= 3 (count (:items r))) (= (:total r) (reduce + 0 (:items r)))))

(ann add-item [Receipt Nat -> Receipt])

(graph till {:states {:receipt Receipt} :edges {:receipt {[add-item Nat] #{:receipt}}}})

(law adding-adds-the-price
  (forall [r Receipt, p Nat] (= (+ p (:total r)) (:total (add-item r p)))))
