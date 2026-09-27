(ns writ.spec-demo.signal-mixed-spec
  "The signal with red left a plain tuple.  An edge into yellow or red then
  says nothing about where a tick from yellow goes: every tuple is in red."
  (:require [writ.spec-demo.signal :refer [GREEN YELLOW]]
            [writ.spec :refer [spec ann refine graph law]]))

(spec writ.spec-demo.signal)

(ann tick [(Tuple Keyword Nat) -> (Tuple Keyword Nat)])

(refine Green  [l (Tuple Keyword Nat)] (and (= :Green (first l)) (<= (second l) GREEN)))
(refine Yellow [l (Tuple Keyword Nat)] (and (= :Yellow (first l)) (<= (second l) YELLOW)))

(graph signal
  {:states {:green Green, :yellow Yellow, :red (Tuple Keyword Nat)}
   :edges  {:green  {[tick] #{:green :yellow}}
            :yellow {[tick] #{:yellow :red}}}})

(law a-light-counts-up-while-it-shows
  (forall [l Green] (=> (< (second l) GREEN) (= (tick l) [:Green (inc (second l))]))))
