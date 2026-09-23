(ns writ.spec-demo.signal-flow-spec
  "A graph whose nodes do not fit the step fn's signature: `tick` takes
  a light, but the graph feeds it a bare Nat."
  (:require [writ.spec-demo.signal :refer [GREEN]]
            [writ.spec :refer [spec ann refine graph]]))

(spec writ.spec-demo.signal)

(ann tick [(Tuple Keyword Nat) -> (Tuple Keyword Nat)])

(refine Green [l (Tuple Keyword Nat)] (and (= :Green (first l)) (<= (second l) GREEN)))

(graph signal
  {:states {:ticks Nat, :green Green}
   :edges  {:ticks {[tick] #{:green}}}})
