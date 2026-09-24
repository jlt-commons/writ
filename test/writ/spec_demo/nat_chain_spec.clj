(ns writ.spec-demo.nat-chain-spec
  (:require [writ.spec :refer [spec ann law graph]]))

(spec writ.spec-demo.nat-chain)

(ann half        [Nat -> Nat])
(ann parity      [Nat -> Nat])
(ann half-by-two [Nat -> Nat])
(ann thirds      [Nat -> Nat])

(graph dividing
  {:states {:n Nat, :part Nat}
   :edges  {:n {[half] #{:part}, [parity] #{:part}, [half-by-two] #{:part}, [thirds] #{:part}}}})

(law half-halves (forall [n Nat] (= (half n) (quot n 2))))
(law parity-is-mod-2 (forall [n Nat] (= (parity n) (mod n 2))))
(law half-by-two-halves (forall [n Nat] (= (half-by-two n) (quot n 2))))
(law thirds-divides (forall [n Nat] (= (thirds n) (quot n 3))))
