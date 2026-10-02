(ns writ.spec-demo.walk-spec
  (:require [writ.spec :refer [spec data ann law graph]]
            [writ.spec-demo.walk :refer [capture clause-of depth]]))

(spec writ.spec-demo.walk)

(data Pattern Wild Nil (Lit Any) (Bind Symbol) (Cons Pattern Pattern))
(data Hit (Hit Nat (Map Symbol Any)) (Miss))

(ann capture [Pattern Any -> Any])
(ann clause-of [(Vec Pattern) Any -> Hit])
(ann depth [Any -> Nat])

(graph walk {:states {:pats (Vec Pattern), :hit Hit} :edges {}})

(def pair [:Cons [:Lit :a] [:Cons [:Bind 'x] [:Nil]]])

(law a-pair-binds-its-second
  (forall [m Any]
    (= (capture pair m)
       (if (and (sequential? m) (= 2 (count m)) (= :a (first m))) {'x (second m)} nil))))

(law the-first-matching-clause-wins
  (forall [m Any]
    (= (clause-of [pair [:Wild]] m)
       (if (some? (capture pair m)) [:Hit 0 (capture pair m)] [:Hit 1 {}]))))

(law a-depth-is-never-negative
  (forall [f Any] (<= 0 (depth f))))

(law a-depth-is-at-most-the-printed-length
  {:require :tested :because "pr-str is not modelled by the prover"}
  (forall [f Any] (<= (depth f) (count (pr-str f)))))
