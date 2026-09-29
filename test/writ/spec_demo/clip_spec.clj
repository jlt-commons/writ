(ns writ.spec-demo.clip-spec
  "Signatures that say more than types: what a result must meet, given
  the arguments, and what the arguments must meet."
  (:require [writ.spec :refer [spec ann refine graph law]]))

(spec writ.spec-demo.clip)

(ann take-upto [(List Nat) Nat -> (List Nat)]
  {:ensures (fn [xs n r] (<= (count r) n))})

(ann clamp [Int Int Int -> Int]
  {:requires (fn [lo hi x] (<= lo hi))
   :ensures  (fn [lo hi x r] (<= lo r hi))})

(ann clamp-digit [Int -> Int])

(refine Digit [d Int] (<= 0 d 9))

(graph digits
  {:states {:any Int, :digit Digit}
   :edges  {:any {[clamp-digit] #{:digit}}}})

(law taking-all-of-a-short-list
  (forall [xs (List Nat)] (= (count xs) (count (take-upto xs (count xs))))))

(law taking-a-prefix
  (forall [xs (List Nat), ys (List Nat)]
    (= (vec xs) (vec (take-upto (concat xs ys) (count xs))))))

(law taking-none
  (forall [xs (List Nat)] (empty? (take-upto xs 0))))

(law a-value-in-range-stays
  (forall [x Int] (=> (<= 0 x 9) (= x (clamp 0 9 x)))))

(law a-value-below-goes-to-the-bottom
  (forall [x Int] (=> (< x 0) (= 0 (clamp 0 9 x)))))

(law a-value-above-goes-to-the-top
  (forall [x Int] (=> (> x 9) (= 9 (clamp 0 9 x)))))

(law clamp-digit-is-clamp
  (forall [x Int] (= (clamp 0 9 x) (clamp-digit x))))
