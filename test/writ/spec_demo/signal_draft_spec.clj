(ns writ.spec-demo.signal-draft-spec
  "A draft of the signal's graph that lets green go straight to red: the
  graph breaks its own rule that red comes only after yellow."
  (:require [writ.spec-demo.signal :refer [GREEN YELLOW RED]]
            [writ.spec :refer [spec ann refine graph]]))

(spec writ.spec-demo.signal)

(ann tick [(Tuple Keyword Nat) -> (Tuple Keyword Nat)])

(refine Green  [l (Tuple Keyword Nat)] (and (= :Green (first l)) (<= (second l) GREEN)))
(refine Yellow [l (Tuple Keyword Nat)] (and (= :Yellow (first l)) (<= (second l) YELLOW)))
(refine Red    [l (Tuple Keyword Nat)] (and (= :Red (first l)) (<= (second l) RED)))

(graph signal
  {:start  [:green [:Green 0]]
   :states {:green Green, :yellow Yellow, :red Red}
   :edges  {:green  {[tick] #{:green :yellow :red}}
            :yellow {[tick] #{:yellow :red}}
            :red    {[tick] #{:red :green}}}
   :before [[:yellow :red]]})
