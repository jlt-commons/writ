(ns writ.spec-demo.frame-tuple-spec
  "A frame on a tuple state, which has no keys."
  (:require [writ.spec :refer [spec ann refine graph law]]))

(spec writ.spec-demo.gauge {:test false})

(ann cool [(Tuple Keyword Int) -> (Tuple Keyword Int)])

(refine Hot  [g (Tuple Keyword Int)] (= :Hot (first g)))
(refine Cold [g (Tuple Keyword Int)] (= :Cold (first g)))

(graph gauge
  {:states {:hot Hot, :cold Cold}
   :edges  {:hot {[cool] {:to #{:hot :cold} :changes [:n]}}}})
