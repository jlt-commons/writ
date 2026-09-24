(ns writ.spec-demo.pipeline-spec
  "The contract for writ.spec-demo.pipeline. The laws say what a request
  gets back; the `calls` forms say how the layers fit together."
  (:require [clojure.string :as str]
            [writ.spec :refer [spec ann law calls graph]]))

(spec writ.spec-demo.pipeline)

(ann normalize [String -> String])
(ann valid?    [String -> Bool])
(ann respond   [String -> (Tuple Keyword String)])
(ann handle    [String -> (Tuple Keyword String)])

(graph request
  {:states {:raw String, :clean String, :valid Bool, :response (Tuple Keyword String)}
   :edges  {:raw   {[normalize] #{:clean}, [handle] #{:response}}
            :clean {[valid?] #{:valid}, [respond] #{:response}}}})

(calls normalize [str/lower-case str/trim])
(calls valid?    [])
(calls respond   [valid?])
(calls handle    [normalize respond])

(defn cleaned [s] (str/lower-case (str/trim s)))

(law handle-answers-with-the-cleaned-input
  (forall [s String] (= (second (handle s)) (cleaned s))))

(law ok-exactly-when-short
  (forall [s String]
    (= (= :ok (first (handle s))) (<= 1 (count (cleaned s)) 8))))
