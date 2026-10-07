(ns writ.spec-demo.receive-spec
  "A scan with literal patterns is the receive the manual describes: proved
  by induction on the scan's index, the match of a literal pattern against
  the message there split on, not opened a level per part of the message."
  (:require [writ.spec :refer [spec data ann law graph refine]]
            [writ.spec-demo.receive :as r]))

(spec writ.spec-demo.receive {:require :proved})

(data Pattern Wild Nil (Lit Any) (Bind Symbol) (Cons Pattern Pattern))
(data Hit (Hit Nat (Map Symbol Any)) (Miss))
(data Scan (Take Nat Nat (Map Symbol Any)) (None Nat))

(ann capture [Pattern Any -> Any])
(ann clause-of [(Vec Pattern) Any -> Hit])
(ann scan [(Vec Any) (Vec Pattern) Nat -> Scan])

(refine Taken  [r Scan] (= :Take (first r)))
(refine Missed [r Scan] (= :None (first r)))

(graph receive
  {:states {:mailbox (Vec Any), :taken Taken, :missed Missed}
   :edges  {:mailbox {[scan (Vec Pattern) Nat] #{:taken :missed}}}
   :tested {:mailbox "capture recurses over a Pattern of any depth"}})

(def p-a [:Cons [:Lit :a] [:Cons [:Bind 'x] [:Nil]]])
(def p-b [:Cons [:Lit :b] [:Cons [:Bind 'y] [:Nil]]])

(defn model-scan
  "The manual's receive, message by message and clause by clause."
  [msgs pats start]
  (or (first (for [i (range start (count msgs))
                   k (range (count pats))
                   :let [env (r/capture (nth pats k) (nth msgs i))]
                   :when (some? env)]
               [:Take i k env]))
      [:None (max start (count msgs))]))

(law scan-is-the-manual
  (forall [msgs (Vec Any), start Nat]
    (= (scan msgs [p-a p-b] start) (model-scan msgs [p-a p-b] start))))

(law the-oldest-message-wins-over-clause-order
  (= (scan [[:b 2] [:a 1]] [p-a p-b] 0) [:Take 0 1 {'y 2}]))
