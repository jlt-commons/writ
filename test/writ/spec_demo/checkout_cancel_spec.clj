(ns writ.spec-demo.checkout-cancel-spec
  "Every state before shipping can be cancelled, which ends a run, and
  pay takes only the exact total: few random runs ship. writ walks runs
  toward a final state the random ones missed."
  (:require [writ.spec :refer [spec ann refine graph]]))

(spec writ.spec-demo.checkout-cancel {:test false})

(ann pay    [(Tuple Keyword Nat) Nat -> (Tuple Keyword Nat)])
(ann ship   [(Tuple Keyword Nat) -> (Tuple Keyword Nat)])
(ann cancel [(Tuple Keyword Nat) -> (Tuple Keyword Nat)])

(refine Placed    [o (Tuple Keyword Nat)] (and (= :placed (first o)) (pos? (second o))))
(refine Paid      [o (Tuple Keyword Nat)] (and (= :paid (first o)) (pos? (second o))))
(refine Shipped   [o (Tuple Keyword Nat)] (and (= :shipped (first o)) (pos? (second o))))
(refine Cancelled [o (Tuple Keyword Nat)] (and (= :cancelled (first o)) (pos? (second o))))

(graph checkout
  {:start  [:placed [:placed 437]]
   :states {:placed Placed, :paid Paid, :shipped Shipped, :cancelled Cancelled}
   :edges  {:placed {[pay Nat] {:to #{:paid} :when (fn [o amt] (= amt (second o)))}
                     [cancel]  #{:cancelled}}
            :paid   {[ship] #{:shipped}
                     [cancel] #{:cancelled}}}
   :final  [:shipped :cancelled]
   :runs   3})
