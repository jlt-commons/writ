(ns writ.spec-demo.admit-spec
  "The laws try a non-member of any age and an adult member, never a
  minor who is a member: the age test never decides alone."
  (:require [writ.spec :refer [spec ann law graph]]))

(spec writ.spec-demo.admit {:test false})

(ann admit [Nat Bool -> Keyword])

(graph door {:states {:age Nat :answer Keyword} :edges {:age {[admit Bool] #{:answer}}}})

(law a-non-member-stays-out (forall [age Nat] (= :out (admit age false))))
(law an-adult-member-comes-in (forall [age Nat] (=> (<= 18 age) (= :in (admit age true)))))
