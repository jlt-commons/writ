(ns writ.spec-demo.no-graph-spec
  "A spec that states laws but no state graph."
  (:require [writ.spec :refer [spec ann law]]))

(spec writ.spec-demo.signal)

(ann tick [(Tuple Keyword Nat) -> (Tuple Keyword Nat)])

(law a-green-light-counts-up (= [:Green 1] (tick [:Green 0])))
