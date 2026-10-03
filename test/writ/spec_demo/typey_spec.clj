(ns writ.spec-demo.typey-spec
  "Two laws that say only what kind of value isort returns: a seq, of
  nats. Neither tells a constant or a truncated answer from the real one,
  and the report names them."
  (:require [writ.spec :refer [spec ann law graph refine]]))
(spec writ.spec-demo.sort {:test false})
(ann insert [Nat (List Nat) -> (List Nat)])
(ann isort [(List Nat) -> (List Nat)])
(defn ascending? [xs] (or (empty? xs) (apply <= xs)))
(refine Sorted [xs (List Nat)] (ascending? xs))
(graph sorting {:states {:unsorted (List Nat), :sorted Sorted} :edges {:unsorted {[isort] #{:sorted}} :sorted {[insert Nat _] #{:sorted}}}})
(law isort-gives-a-seq (forall [xs (List Nat)] (seqable? (isort xs))))
(law isort-gives-nats (forall [xs (List Nat)] (every? nat-int? (isort xs))))
