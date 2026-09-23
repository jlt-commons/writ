(ns writ.spec-demo.nat-chain-spec
  (:require [writ.spec :refer [spec ann law]]))

(spec writ.spec-demo.nat-chain)

(ann half        [Nat -> Nat])
(ann parity      [Nat -> Nat])
(ann half-by-two [Nat -> Nat])
(ann thirds      [Nat -> Nat])

(law half-halves (forall [n Nat] (= (half n) (quot n 2))))
(law parity-is-mod-2 (forall [n Nat] (= (parity n) (mod n 2))))
(law half-by-two-halves (forall [n Nat] (= (half-by-two n) (quot n 2))))
(law thirds-divides (forall [n Nat] (= (thirds n) (quot n 3))))
