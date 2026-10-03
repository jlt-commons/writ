(ns writ.spec-demo.checkout-locked-spec
  "A guard no amount meets from the start: an odd amount equal to an even
  total. No run gets past :placed, and the report says which guard kept
  refusing."
  (:require [writ.spec :refer [spec ann refine graph]]))

(spec writ.spec-demo.checkout {:test false})

(ann pay  [(Tuple Keyword Nat) Nat -> (Tuple Keyword Nat)])
(ann ship [(Tuple Keyword Nat) -> (Tuple Keyword Nat)])

(refine Placed  [o (Tuple Keyword Nat)] (and (= :placed (first o)) (pos? (second o))))
(refine Paid    [o (Tuple Keyword Nat)] (and (= :paid (first o)) (pos? (second o))))
(refine Shipped [o (Tuple Keyword Nat)] (and (= :shipped (first o)) (pos? (second o))))

(graph checkout
  {:start  [:placed [:placed 438]]
   :states {:placed Placed, :paid Paid, :shipped Shipped}
   :edges  {:placed {[pay Nat] {:to #{:paid} :when (fn [o amt] (and (= amt (second o)) (odd? amt)))}}
            :paid   {[ship] #{:shipped}}}
   :final  [:shipped]
   :runs   10})
