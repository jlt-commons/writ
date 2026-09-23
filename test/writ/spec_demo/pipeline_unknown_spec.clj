(ns writ.spec-demo.pipeline-unknown-spec
  "A `calls` form naming fns the target does not define."
  (:require [writ.spec :refer [spec ann law calls]]))

(spec writ.spec-demo.pipeline)

(ann handle [String -> (Tuple Keyword String)])

(calls handle [normalise respond])
(calls render [respond])

(law handle-keeps-short-input
  (forall [s String] (= (second (handle s)) (clojure.string/lower-case (clojure.string/trim s)))))
