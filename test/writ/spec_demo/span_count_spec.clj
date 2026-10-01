(ns writ.spec-demo.span-count-spec
  "Overlap as a unit counted twice among both spans' units, through
  frequencies, which the prover does not read: the law is only tested.
  The naive test is wrong on about one pair in a hundred, so a hundred
  trials miss it a third of the time."
  (:require [writ.spec :refer [spec ann refine graph law]]))

(spec writ.spec-demo.span {:test false})

(refine Span [s {:start Nat, :end Nat}] true)

(ann overlaps? [Span Span -> Bool])

(graph spans {:states {:span Span, :any Bool}
              :edges {:span {[overlaps? Span] #{:any}}}})

(defn shared? [a b]
  (boolean (some #(= 2 (val %)) (frequencies (concat (range (:start a) (:end a)) (range (:start b) (:end b)))))))

(law overlap-is-a-shared-unit
  (forall [a Span, b Span] (= (overlaps? a b) (shared? a b))))
