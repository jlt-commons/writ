(ns writ.spec-demo.alarms-spec
  "A field typed by a refinement: induction over a vector of the type
  keeps its hypothesis."
  (:require [writ.spec :refer [spec data ann refine law graph]]))

(spec writ.spec-demo.alarms {:require :proved})

(refine Every [e Any] (or (nil? e) (nat-int? e)))
(data Alarm (Alarm Any Every))

(ann cancel [(Vec Alarm) Any -> (Vec Alarm)])

(graph alarms {:states {:t (Vec Alarm)} :edges {:t {[cancel Any] #{:t}}}})

(law cancelling-what-is-not-there-changes-nothing
  (forall [t (Vec Alarm), r Any]
    (=> (not-any? (fn [x] (case (first x) :Alarm (let [[_ ref] x] (= r ref)))) t)
        (= (cancel t r) t))))
