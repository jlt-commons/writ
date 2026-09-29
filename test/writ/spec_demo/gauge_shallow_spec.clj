(ns writ.spec-demo.gauge-shallow-spec
  "Runs too short to cool the gauge: no run reaches the final state."
  (:require [writ.spec :refer [spec ann refine graph invariant law]]
            [writ.spec-demo.gauge :refer [cool]]))

(spec writ.spec-demo.gauge)

(ann cool [(Tuple Keyword Int) -> (Tuple Keyword Int)])

(refine Hot  [g (Tuple Keyword Int)] (= :Hot (first g)))
(refine Cold [g (Tuple Keyword Int)] (= :Cold (first g)))

(graph gauge
  {:start  [:hot [:Hot 8]]
   :states {:hot Hot, :cold Cold}
   :edges  {:hot {[cool] #{:hot :cold}}}
   :final  [:cold]
   :runs   5
   :depth  2})
