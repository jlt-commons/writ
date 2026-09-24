(ns writ.spec-demo.pipeline-layers-spec
  "The pipeline's layers stated as reach, not as exact call sets: `handle`
  goes through `respond`, which decides validity, and nothing it reaches
  upper-cases a request."
  (:require [clojure.string :as str]
            [writ.spec :refer [spec ann law calls graph]]))

(spec writ.spec-demo.pipeline)

(ann normalize [String -> String])
(ann valid?    [String -> Bool])
(ann respond   [String -> (Tuple Keyword String)])
(ann handle    [String -> (Tuple Keyword String)])

(graph request
  {:states {:raw String, :response (Tuple Keyword String)}
   :edges  {:raw {[handle] #{:response}}}})

(calls handle {:through [normalize respond valid?] :not [str/upper-case]})

(defn cleaned [s] (str/lower-case (str/trim s)))

(law handle-answers-with-the-cleaned-input
  (forall [s String] (= (second (handle s)) (cleaned s))))

(law ok-exactly-when-short
  (forall [s String]
    (= (= :ok (first (handle s))) (<= 1 (count (cleaned s)) 8))))
