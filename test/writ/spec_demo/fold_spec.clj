(ns writ.spec-demo.fold-spec
  "Over no items the fold is its start, whatever its step: proved, though
  the step is outside the prover."
  (:require [writ.spec :refer [spec ann law graph]]))

(spec writ.spec-demo.fold {:require :proved})

(ann run-all [Nat (Vec Nat) -> (Tuple Nat (Vec Nat))])

(graph g {:states {:n Nat, :out (Tuple Nat (Vec Nat))} :edges {:n {[run-all (Vec Nat)] #{:out}}}})

(law nothing-runs-nothing (forall [c Nat] (= (run-all c []) [c []])))

(law one-item-is-counted
  {:require :tested :because "the step conjes onto an accumulator the prover reads as any value"}
  (forall [c Nat, x Nat] (= (run-all c [x]) [(+ c x) [x]])))
