(ns writ.spec-demo.roster-spec
  "A child read by its place is found by its id: proved by induction on
  the children, its place read from their tail, a list that may be nil
  were the place not inside it."
  (:require [writ.spec :refer [spec ann refine law graph]]))

(spec writ.spec-demo.roster {:require :proved})

(refine Restart [r Keyword] (contains? #{:permanent :transient :temporary} r))

(ann index-of [(List Nat) Nat -> Any])

(graph roster {:states {:ids (List Nat) :at Any}
               :edges {:ids {[index-of Nat] #{:at}}}})

(law a-found-index-is-a-position
  (forall [ids (List Nat), id Nat]
    (=> (some? (index-of ids id))
        (and (integer? (index-of ids id)) (<= 0 (index-of ids id))))))

(law a-child-index-is-a-position
  (forall [cs (Vec (Tuple Nat Restart)), id Nat]
    (=> (some? (index-of (mapv first cs) id))
        (and (integer? (index-of (mapv first cs) id)) (<= 0 (index-of (mapv first cs) id))))))

(law a-child-present-has-an-index
  (forall [cs (Vec (Tuple Nat Restart)), i Nat]
    (=> (< i (count cs))
        (integer? (index-of (mapv first cs) (first (nth cs i)))))))

(law index-of-example (= (index-of [4 7 9] 7) 1))
