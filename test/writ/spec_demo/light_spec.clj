(ns writ.spec-demo.light-spec
  (:require [writ.spec :refer [spec data ann law graph]]))

(spec writ.spec-demo.light)

(data Light Red Amber Green)

(ann tick [(Tuple Light Nat) -> (Tuple Light Nat)])

(graph light
  {:states {:showing (Tuple Light Nat)}
   :edges  {:showing {[tick] #{:showing}}}})

(law a-light-holds-for-three-ticks
  (forall [n Nat] (= [[:Red] (inc n)] (tick [[:Red] n]))))
