(ns writ.spec-demo.ref-spec
  "Laws about when code throws, and laws over every fn of a type."
  (:require [writ.spec :refer [spec ann refine graph law throws?]]))

(spec writ.spec-demo.ref)

(ann at         [(Vec Nat) Nat -> Nat])
(ann keep-where [(-> Nat Bool) (List Nat) -> (List Nat)])

(graph reading
  {:states {:vec (Vec Nat), :kept (List Nat)}
   :edges  {}})

(law reading-past-the-end-throws
  (forall [v (Vec Nat), i Nat] (= (throws? (at v i)) (>= i (count v)))))

(law reading-inside-gives-the-element
  (forall [v (Vec Nat), i Nat] (=> (< i (count v)) (= (nth v i) (at v i)))))

(law what-is-kept-passes
  (forall [p (-> Nat Bool), xs (List Nat)] (every? p (keep-where p xs))))

(law what-passes-is-kept
  (forall [p (-> Nat Bool), xs (List Nat)]
    (= (count (filter p xs)) (count (keep-where p xs)))))

(law keeping-goes-in-order
  (forall [p (-> Nat Bool), xs (List Nat), ys (List Nat)]
    (= (keep-where p (concat xs ys)) (concat (keep-where p xs) (keep-where p ys)))))
