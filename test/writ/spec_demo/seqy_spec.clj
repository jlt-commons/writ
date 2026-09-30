(ns writ.spec-demo.seqy-spec
  "Two false laws the prover must not prove."
  (:require [writ.spec :refer [spec ann graph law]]))

(spec writ.spec-demo.seqy)

(ann head-or [(List Nat) -> Any])
(ann second-or [(List Nat) -> Any])
(ann pick [(List String) -> Nat])

(graph seqy
  {:states {:xs (List Nat), :x Any}
   :edges  {:xs {[head-or] #{:x}, [second-or] #{:x}}}})

(law head-and-second-agree-on-nil
  (forall [xs (List Nat)] (= (nil? (head-or xs)) (nil? (second-or xs)))))

(law always-picks-one (forall [xs (List String)] (= 1 (pick xs))))
