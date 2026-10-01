(ns writ.spec-demo.span-rare-spec
  "A hypothesis that holds in about one trial in five hundred -- two spans
  of one length, back to back -- in a law the prover does not read. A
  hundred trials may meet it never, and then more are run. It names no
  number, so writ's seeding of the spec's numbers does not make it common."
  (:require [clojure.set :as set]
            [writ.spec :refer [spec ann refine graph law]]))

(spec writ.spec-demo.span {:test false})

(refine Span [s {:start Nat, :end Nat}] true)

(ann overlaps? [Span Span -> Bool])

(graph spans {:states {:span Span, :any Bool}
              :edges {:span {[overlaps? Span] #{:any}}}})

(defn units [s] (set (range (:start s) (:end s))))

(defn shared? [a b]
  (boolean (some #(= 2 (val %)) (frequencies (concat (range (:start a) (:end a)) (range (:start b) (:end b)))))))

(law back-to-back-spans-of-one-length-overlap-where-they-share-a-unit
  (forall [a Span, b Span]
    (=> (and (pos? (count (units a))) (= (count (units a)) (count (units b))) (= (:end a) (:start b)))
        (= (overlaps? a b) (shared? a b)))))
