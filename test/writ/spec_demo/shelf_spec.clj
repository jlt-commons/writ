(ns writ.spec-demo.shelf-spec
  "A shelf whose :done state has no edges out and is not declared final:
  the graph does not say the run may end there."
  (:require [writ.spec :refer [spec ann refine graph]]
            [writ.spec-demo.shelf :refer [fill]]))

(spec writ.spec-demo.shelf)

(ann fill [(Tuple Keyword Int) -> (Tuple Keyword Int)])

(refine Open [s (Tuple Keyword Int)] (and (= :Open (first s)) (<= 0 (second s)) (<= (second s) 2)))
(refine Done [s (Tuple Keyword Int)] (and (= :Done (first s)) (zero? (second s))))

(graph shelf
  {:start  [:open [:Open 0]]
   :states {:open Open, :done Done}
   :edges  {:open {[fill] #{:open :done}}}})
