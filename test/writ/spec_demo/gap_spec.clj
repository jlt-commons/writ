(ns writ.spec-demo.gap-spec
  "A law whose hypothesis no generated input meets: a generated Int stays
  within 50 of 0, so a is never 3(b + 40), at least 120. The solver finds
  inputs that meet it."
  (:require [writ.spec :refer [spec ann refine graph law]]))

(spec writ.spec-demo.gap {:test false})

(ann gap [Int Int -> Int])

(refine Far [n Int] (> n 90))

(graph distance
  {:states {:n Int, :far Far}
   :edges  {:far {[gap Int] #{:n}}}})

(law far-apart
  (forall [a Int, b Int] (=> (= a (* 3 (+ b 40))) (= (+ (* 2 b) 120) (gap a b)))))
