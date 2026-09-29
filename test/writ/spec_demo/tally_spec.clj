(ns writ.spec-demo.tally-spec
  "frequencies is outside the prover; an assumption about it, tested
  against clojure.core on every check, lets the tally's law be proved."
  (:require [writ.spec :refer [spec ann graph law assume]]))

(spec writ.spec-demo.tally {:require :proved})

(assume clojure.core/frequencies [(List Nat) -> (Map Nat Nat)])
(assume the-counts-add-up
  (forall [xs (List Nat)] (= (apply + (vals (frequencies xs))) (count xs))))

(ann tally [(List Nat) -> (Map Nat Nat)])

(graph tallying {:states {:xs (List Nat), :counts (Map Nat Nat)} :edges {:xs {[tally] #{:counts}}}})

(law every-value-is-counted
  (forall [xs (List Nat)] (= (count xs) (apply + (vals (tally xs))))))

(law each-count-is-how-often
  (forall [xs (List Nat), x Nat] (= (get (tally xs) x 0) (count (filter #(= x %) xs)))))
