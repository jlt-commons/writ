(ns writ.spec-demo.hits-user-spec
  "The workflow's contract over the component's Hits: its graph lands in
  Hits, read through the component's own predicate and helper."
  (:require [writ.spec :refer [spec ann law graph]]))

(spec writ.spec-demo.hits-user {:test false :uses [writ.spec-demo.hits-spec]})

(ann add-twice [Hits Nat -> Hits])

(graph twice {:states {:hits Hits} :edges {:hits {[add-twice Nat] #{:hits}}}})

(law adding-twice-adds-twice
  (forall [h Hits, n Nat] (= (+ (:count h) n n) (:count (add-twice h n)))))
