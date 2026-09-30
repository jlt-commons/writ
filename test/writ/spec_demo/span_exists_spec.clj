(ns writ.spec-demo.span-exists-spec
  "Overlap as a unit both spans hold, said with exists. A unit t between
  bounds exists when each lower bound is at most each upper one, so the
  law is read without the exists, and proved or refuted outright."
  (:require [writ.spec :refer [spec ann refine graph law]]))

(spec writ.spec-demo.span {:test false})

(refine Span [s {:start Nat, :end Nat}] true)

(ann overlaps? [Span Span -> Bool])

(graph spans {:states {:span Span, :any Bool}
              :edges {:span {[overlaps? Span] #{:any}}}})

(defn holds? [s t] (and (<= (:start s) t) (< t (:end s))))

(law overlap-means-a-shared-unit
  (forall [a Span, b Span]
    (=> (overlaps? a b) (exists [t Nat] (and (holds? a t) (holds? b t))))))

(law a-shared-unit-means-overlap
  (forall [a Span, b Span]
    (=> (exists [t Nat] (and (holds? a t) (holds? b t))) (overlaps? a b))))
