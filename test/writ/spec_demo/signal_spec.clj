(ns writ.spec-demo.signal-spec
  "The signal's state graph. Each phase is a refinement of the light's
  type, and each edge says where a tick may take a light in that phase.
  writ proves every edge from the code, so the graph's own rules --
  red only ever comes after yellow -- hold for every run of `tick`."
  (:require [writ.spec-demo.signal :refer [GREEN YELLOW RED]]
            [writ.spec :refer [spec ann refine graph law]]))

(spec writ.spec-demo.signal {:require :proved})

(ann tick [(Tuple Keyword Nat) -> (Tuple Keyword Nat)])

(refine Green  [l (Tuple Keyword Nat)] (and (= :Green (first l)) (<= (second l) GREEN)))
(refine Yellow [l (Tuple Keyword Nat)] (and (= :Yellow (first l)) (<= (second l) YELLOW)))
(refine Red    [l (Tuple Keyword Nat)] (and (= :Red (first l)) (<= (second l) RED)))

(graph signal
  {:start  [:green [:Green 0]]
   :states {:green Green, :yellow Yellow, :red Red}
   :edges  {:green  {[tick] #{:green :yellow}}
            :yellow {[tick] #{:yellow :red}}
            :red    {[tick] #{:red :green}}}
   :before [[:yellow :red]]})

(law a-light-counts-up-while-it-shows
  (forall [l Green] (=> (< (second l) GREEN) (= (tick l) [:Green (inc (second l))]))))
