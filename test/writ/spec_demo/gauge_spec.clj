(ns writ.spec-demo.gauge-spec
  "A gauge's state graph with an invariant: while hot, its count is
  even.  Every edge that may land in :hot carries the predicate as its
  own obligation, and the start value must satisfy it too."
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

(invariant gauge :hot [g] (even? (second g)))

(law a-hot-gauge-cools (forall [g Hot] (or (= :Cold (first (cool g)))
                                           (< (second (cool g)) (second g)))))
