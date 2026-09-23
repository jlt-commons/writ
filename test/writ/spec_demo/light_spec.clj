(ns writ.spec-demo.light-spec
  (:require [writ.spec :refer [spec data ann law]]))

(spec writ.spec-demo.light)

(data Light Red Amber Green)

(ann tick [(Tuple Light Nat) -> (Tuple Light Nat)])

(law a-light-holds-for-three-ticks
  (forall [n Nat] (= [[:Red] (inc n)] (tick [[:Red] n]))))
