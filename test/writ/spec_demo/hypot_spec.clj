(ns writ.spec-demo.hypot-spec
  "Math/sqrt and Math/abs are pure: the spec assumes their signatures, so
  the code may call them."
  (:require [writ.spec :refer [spec ann refine graph law assume]]))

(spec writ.spec-demo.hypot {:require :tested})

(assume Math/sqrt [Double -> Double])
(assume java.lang.Math/abs [Double -> Double])

(assume sqrt-is-not-negative
  (forall [x Double] (not (neg? (Math/sqrt x)))))

(ann hypot [Double Double -> Double])
(ann norm  [Double Double -> Double])

(refine Length [d Double] (not (neg? d)))

(graph measuring
  {:states {:coord Double, :length Length}
   :edges  {:coord {[hypot Double] #{:length}
                    [norm Double]  #{:length}}}})

(law three-four-five
  (= (hypot 3.0 4.0) 5.0))

(law along-an-axis-it-is-the-distance
  (forall [x Double] (= (hypot x 0.0) (Math/abs x))))

(law hypot-is-not-negative
  (forall [x Double y Double] (not (neg? (hypot x y)))))

(law hypot-is-symmetric
  (forall [x Double y Double] (= (hypot x y) (hypot y x))))

(law norm-is-hypot
  (forall [x Double y Double] (= (norm x y) (hypot x y))))
