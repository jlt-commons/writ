(ns writ.spec-demo.lending-spec
  "Members are built by `spread`, which puts half of them owing an odd
  amount near the block -- never exactly 500. The block is in the code,
  and writ sets a built value's integers to the code's numbers now and
  then, so 500 itself is tried."
  (:require [writ.spec :refer [spec ann refine graph law]]))

(spec writ.spec-demo.lending {:test false})

(defn spread [m] (update m :fines #(if (odd? %) (+ 490 (* 2 (mod % 10)) 1) %)))

(refine Member [m {:id Nat, :fines Nat}] true {:build spread})
(refine Allowed [b Bool] b)

(ann may-borrow? [Member -> Bool])

(graph desk {:states {:member Member, :answer Bool}
             :edges {:member {[may-borrow?] #{:answer}}}})

(law owing-less-than-the-block-may-borrow
  (forall [m Member] (= (may-borrow? m) (< (:fines m) 500))))
