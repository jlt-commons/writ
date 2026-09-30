(ns writ.spec-demo.pick-spec
  (:require [writ.spec :refer [spec ann graph law]]))

(spec writ.spec-demo.pick {:test false})

(ann pick [Bool -> String])

(graph picking {:states {:b Bool, :s String} :edges {:b {[pick] #{:s}}}})

(law true-picks-one (forall [b Bool] (=> b (= "one" (pick b)))))
