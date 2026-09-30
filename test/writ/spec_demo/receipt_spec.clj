(ns writ.spec-demo.receipt-spec
  "A receipt's total is the sum of its items. A random receipt almost
  never has that, so its values are built to fit: `settle` makes any
  receipt one, and the refinement's :build says so."
  (:require [writ.spec :refer [spec ann refine graph law]]))

(spec writ.spec-demo.receipt {:test false})

(defn settle [r] (assoc r :total (reduce + 0 (:items r))))

(refine Receipt [r {:items (Vec Nat), :total Nat}] (= (:total r) (reduce + 0 (:items r)))
  {:build settle})

(ann add-item [Receipt Nat -> Receipt])

(graph till {:states {:receipt Receipt} :edges {:receipt {[add-item Nat] #{:receipt}}}})

(law adding-adds-the-price
  (forall [r Receipt, p Nat] (= (+ p (:total r)) (:total (add-item r p)))))
