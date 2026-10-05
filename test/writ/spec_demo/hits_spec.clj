(ns writ.spec-demo.hits-spec
  "The component's contract: a Hits is a count no lower than zero, said
  by a helper of this spec."
  (:require [writ.spec :refer [spec ann law graph refine]]))

(spec writ.spec-demo.hits {:test false})

(defn sane? [h] (<= 0 (:count h)))

(refine Hits [h {:count Int}] (sane? h))

(ann add-hits [Hits Nat -> Hits])

(graph hits {:states {:hits Hits} :edges {:hits {[add-hits Nat] #{:hits}}}})

(law adding-adds (forall [h Hits, n Nat] (= (+ (:count h) n) (:count (add-hits h n)))))
