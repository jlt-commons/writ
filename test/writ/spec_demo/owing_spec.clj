(ns writ.spec-demo.owing-spec
  "A law the prover does not prove -- it counts with frequencies -- comparing a
  computed sum with 500. writ asks the solver for inputs where the sum is
  499, 500 and 501, and runs the law there."
  (:require [writ.spec :refer [spec ann refine graph law]]))

(spec writ.spec-demo.owing {:test false})

(refine Banned [t Keyword] (= :banned t))

(ann may-borrow? [Nat Nat (List Keyword) -> Bool])

(graph desk {:states {:fines Nat, :answer Bool}
             :edges {:fines {[may-borrow? Nat (List Keyword)] #{:answer}}}})

(law owing-less-than-500-and-not-banned-may-borrow
  (forall [f Nat, g Nat, tags (List Keyword)]
    (= (may-borrow? f g tags)
       (and (< (+ f (* 2 g)) 500) (not (contains? (frequencies tags) :banned))))))
