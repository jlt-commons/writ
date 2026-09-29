(ns writ.spec-demo.ref-misuse-spec
  "A throws? law that only holds because the call breaks at's signature:
  a type error is writ's, not the code's."
  (:require [writ.spec :refer [spec ann graph law throws?]]))

(spec writ.spec-demo.ref {:test false})

(ann at         [(Vec Nat) Nat -> Nat])
(ann keep-where [(-> Nat Bool) (List Nat) -> (List Nat)])

(graph reading {:states {:vec (Vec Nat)} :edges {}})

(law a-negative-index-throws
  (forall [v (Vec Nat)] (throws? (at v -1))))
