(ns writ.spec-demo.gauge-vacuous-spec
  "An invariant the state's own refinement already says: every Hot is
  :Hot, so it constrains nothing."
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
   :final  [:cold]})

(invariant gauge :hot [g] (= :Hot (first g)))
