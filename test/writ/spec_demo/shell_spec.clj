(ns writ.spec-demo.shell-spec
  "The pipeline's spec, with the shell's wiring: `serve` hands each line
  to the pipeline's `handle`, and never answers it with `respond` alone."
  (:require [writ.spec-demo.shell :as shell]
            [writ.spec-demo.pipeline :as p]
            [writ.spec :refer [spec ann law calls graph flow]]))

(spec writ.spec-demo.pipeline)

(ann normalize [String -> String])
(ann valid?    [String -> Bool])
(ann respond   [String -> (Tuple Keyword String)])
(ann handle    [String -> (Tuple Keyword String)])

(graph request
  {:states {:raw String, :response (Tuple Keyword String)}
   :edges  {:raw {[handle] #{:response}}}})

(calls shell/serve     {:through [p/handle]})
(calls shell/serve-raw {:through [p/handle]})
(flow shell/serve [line] [line p/handle show :result])

(law answers (forall [s String] (keyword? (first (handle s)))))
(law ok-exactly-when-short
  (forall [s String]
    (= (= :ok (first (handle s)))
       (<= 1 (count (clojure.string/lower-case (clojure.string/trim s))) 8))))
(law keeps-the-cleaned-input
  (forall [s String]
    (= (second (handle s)) (clojure.string/lower-case (clojure.string/trim s)))))
