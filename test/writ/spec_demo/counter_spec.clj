(ns writ.spec-demo.counter-spec
  "A counter's state graph with runs.  The high climb's edge is let off
  proof and only sampled, so a drift at a rare count can slip past a
  sample; a run walks the real steps from the start and reaches it."
  (:require [writ.spec :refer [spec ann refine graph law]]
            [writ.spec-demo.counter :refer [step]]))

(spec writ.spec-demo.counter)

(ann step [(Tuple Keyword Int) -> (Tuple Keyword Int)])

(refine LowBand  [c (Tuple Keyword Int)] (and (= :Low (first c)) (<= 0 (second c)) (<= (second c) 4)))
(refine HighBand [c (Tuple Keyword Int)] (and (= :High (first c))
                                              (zero? (rem (second c) 5))
                                              (<= 10 (second c))))

(graph counter
  {:start  [:low [:Low 0]]
   :states {:low LowBand, :high HighBand}
   :edges  {:low  {[step] #{:low :high}}
            :high {[step] #{:high}}}
   :tested {:high "the climb is long; proof of every multiple of five is left to runs"}
   :runs   50
   :depth  30})

(law a-low-count-climbs (forall [c LowBand] (< (second c) (second (step c)))))
(law a-high-count-climbs (forall [c HighBand] (< (second c) (second (step c)))))
