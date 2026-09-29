(ns writ.spec-demo.spin-spec
  "A graph whose only loop never reaches its final state."
  (:require [writ.spec :refer [spec ann refine graph]]
            [writ.spec-demo.spin :refer [flip]]))

(spec writ.spec-demo.spin)

(ann flip [(Tuple Keyword Int) -> (Tuple Keyword Int)])

(refine A    [s (Tuple Keyword Int)] (= :A (first s)))
(refine B    [s (Tuple Keyword Int)] (= :B (first s)))
(refine Done [s (Tuple Keyword Int)] (= :Done (first s)))

(graph spin
  {:start  :a
   :states {:a A, :b B, :done Done}
   :edges  {:a {[flip] #{:b}}
            :b {[flip] #{:a}}}
   :final  [:done]})
