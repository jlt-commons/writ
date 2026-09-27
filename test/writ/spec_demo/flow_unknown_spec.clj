(ns writ.spec-demo.flow-unknown-spec
  "Flows that name what the target does not have."
  (:require [writ.spec :refer [spec ann law flow graph refine]]))

(spec writ.spec-demo.pipeline)

(ann normalize [String -> String])
(ann respond   [String -> (Tuple Keyword String)])
(ann handle    [String -> (Tuple Keyword String)])

(graph request
  {:states {:raw String, :response (Tuple Keyword String)}
   :edges  {:raw {[handle] #{:response}}}})

(flow handle [s] [s sanitize respond])
(flow handle [s t] [s normalize])

(law answers (forall [s String] (keyword? (first (handle s)))))
