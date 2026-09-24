(ns writ.spec-demo.sort-lemma-proof
  "How writ.spec-demo.sort-lemma-spec is proved: the lemma its `sorted`
  law needs, and a hint where to look."
  (:require [writ.spec :refer [proof-of lemma hint]]))

(proof-of writ.spec-demo.sort-lemma-spec)

(lemma insert-keeps-sorted
  (forall [x Nat, xs (List Nat)]
    (=> (writ.spec-demo.sort-lemma-spec/ascending? xs)
        (writ.spec-demo.sort-lemma-spec/ascending? (insert x xs)))))

(hint sorted {:induct xs :use [insert-keeps-sorted]})
