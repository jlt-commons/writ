(ns writ.spec-demo.sort-false-lemma-proof
  "A proof namespace with a lemma that is false of the code."
  (:require [writ.spec :refer [proof-of lemma]]))

(proof-of writ.spec-demo.sort-lemma-spec)

(lemma insert-keeps-length
  (forall [x Nat, xs (List Nat)] (= (count (insert x xs)) (count xs))))
