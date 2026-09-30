(ns writ.spec-demo.span-spec
  "Overlap as the units two spans share, by sets, which the prover does
  not read: the law is only tested. The naive test is wrong on about one
  pair in a hundred, so a hundred trials miss it a third of the time."
  (:require [clojure.set :as set]
            [writ.spec :refer [spec ann refine graph law]]))

(spec writ.spec-demo.span {:test false})

(refine Span [s {:start Nat, :end Nat}] true)
(refine Hit [b Bool] b)

(ann overlaps? [Span Span -> Bool])

(graph spans {:states {:span Span, :hit Hit, :any Bool}
              :edges {:span {[overlaps? Span] #{:any}}}})

(defn units [s] (set (range (:start s) (:end s))))

(law overlap-is-a-shared-unit
  (forall [a Span, b Span]
    (= (overlaps? a b) (boolean (seq (set/intersection (units a) (units b)))))))
