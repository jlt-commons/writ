(ns writ.spec-demo.gate-spec
  "Only says what happens to those who are not members: the and that lets
  someone in is never true."
  (:require [writ.spec :refer [spec ann law graph]]))

(spec writ.spec-demo.gate {:require :tested})

(ann admit [Nat Bool -> Keyword])
(ann holder [(Map Nat {:who Nat}) Nat Nat -> Keyword])
(ann badges [(Vec Nat) -> (Vec Nat)])

(graph door {:states {:age Nat, :verdict Keyword} :edges {:age {[admit Bool] #{:verdict}}}})

(law strangers-stay-out (forall [age Nat] (= :out (admit age false))))

(law a-holder-is-who-booked
  (forall [m (Map Nat {:who Nat}), id Nat, who Nat]
    (= (holder m id who) (if (= who (get-in m [id :who])) :theirs :not))))

(law badges-are-the-adults (forall [xs (Vec Nat)] (= (badges xs) (filterv #(<= 18 %) xs))))
