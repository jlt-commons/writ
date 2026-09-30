(ns writ.spec-demo.span-rare-spec
  "A hypothesis that holds in a trial or two in a hundred -- a span of
  exactly seven units -- in a law the prover does not read. A hundred
  trials may meet it never, and then more are run."
  (:require [clojure.set :as set]
            [writ.spec :refer [spec ann refine graph law]]))

(spec writ.spec-demo.span {:test false})

(refine Span [s {:start Nat, :end Nat}] true)

(ann overlaps? [Span Span -> Bool])

(graph spans {:states {:span Span, :any Bool}
              :edges {:span {[overlaps? Span] #{:any}}}})

(defn units [s] (set (range (:start s) (:end s))))

(law a-seven-unit-span-overlaps-what-it-shares-a-unit-with
  (forall [a Span, b Span]
    (=> (= 7 (count (units a)))
        (= (overlaps? a b) (boolean (seq (set/intersection (units a) (units b))))))))
