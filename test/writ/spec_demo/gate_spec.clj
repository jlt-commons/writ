(ns writ.spec-demo.gate-spec
  "Only says what happens to those who are not members: the and that lets
  someone in is never true."
  (:require [writ.spec :refer [spec ann law graph]]))

(spec writ.spec-demo.gate {:require :tested})

(ann admit [Nat Bool -> Keyword])

(graph door {:states {:age Nat, :verdict Keyword} :edges {:age {[admit Bool] #{:verdict}}}})

(law strangers-stay-out (forall [age Nat] (= :out (admit age false))))
