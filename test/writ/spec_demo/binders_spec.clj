(ns writ.spec-demo.binders-spec
  "A graph edge out of a vector refinement over its elements, which a proof
  must give up on within the law's budget."
  (:require [writ.spec :refer [spec ann refine graph law]]))

(spec writ.spec-demo.binders {:require :proved})

(ann atom-binder [Any -> (List Symbol)])
(ann tuple-binders [(List Any) -> (List Symbol)])
(ann bound-syms [Any -> (List Symbol)])

(refine Binder   [f (Vec Symbol)] (boolean (some #(not= '_ %) f)))
(refine AnyNames [xs (List Symbol)] (not (empty? xs)))

(graph binders
  {:states {:binder Binder, :names AnyNames}
   :edges  {:binder {[bound-syms] #{:names}}}
   :tested {:binder "a tuple form of unknown length needs induction"}})

(law a-repeated-binder-is-named-once
  (= (vec (bound-syms '[a a b])) '[a b]))
