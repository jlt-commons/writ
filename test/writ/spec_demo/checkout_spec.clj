(ns writ.spec-demo.checkout-spec
  "An exact guard: pay goes through only with the order's own total. A
  random amount is almost never that, so a run has to look for an amount
  the guard takes to get past :placed."
  (:require [writ.spec :refer [spec ann refine graph]]))

(spec writ.spec-demo.checkout {:test false})

(ann pay  [(Tuple Keyword Nat) Nat -> (Tuple Keyword Nat)])
(ann ship [(Tuple Keyword Nat) -> (Tuple Keyword Nat)])

(refine Placed  [o (Tuple Keyword Nat)] (and (= :placed (first o)) (pos? (second o))))
(refine Paid    [o (Tuple Keyword Nat)] (and (= :paid (first o)) (pos? (second o))))
(refine Shipped [o (Tuple Keyword Nat)] (and (= :shipped (first o)) (pos? (second o))))

(graph checkout
  {:start  [:placed [:placed 437]]
   :states {:placed Placed, :paid Paid, :shipped Shipped}
   :edges  {:placed {[pay Nat] {:to #{:paid} :when (fn [o amt] (= amt (second o)))}}
            :paid   {[ship] #{:shipped}}}
   :final  [:shipped]
   :runs   10})
