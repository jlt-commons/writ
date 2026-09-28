(ns writ.spec-demo.tagged-without-spec
  (:require [writ.spec :refer [spec data ann refine graph law]]))

(spec writ.spec-demo.tagged)

(data Answer (Hit Any) (Miss))
(ann answer [Any Any -> Answer])
(refine Hits [a Answer] (= :Hit (first a)))
(refine Misses [a Answer] (= :Miss (first a)))

(graph reply
  {:states {:msg Any, :hit Hits, :miss Misses}
   :edges  {:msg {[answer _ Any] #{:hit :miss}}}})

(law a-tagged-message-hits (forall [v Any] (= (answer ["abcd" v] "abcd") [:Hit v])))
