(ns orders.core-spec
  "The contract for orders.core: an order moves from cart to delivered, or
  is cancelled before it ships, and money only moves the way the steps say."
  (:require [writ.spec :refer [spec ann law graph refine]]))

(spec orders.core)

(refine Status [s Keyword] (contains? #{:cart :placed :paid :shipped :delivered :cancelled} s))
(refine Order [o {:status Status, :total Nat, :paid Nat, :refunded Nat}]
  (<= (:refunded o) (:paid o)))

(defn unpaid? [o] (and (zero? (:paid o)) (zero? (:refunded o))))
(defn paid-in-full? [o] (and (pos? (:total o)) (= (:paid o) (:total o))))

(refine Cart      [o Order] (and (= :cart (:status o)) (unpaid? o)))
(refine Placed    [o Order] (and (= :placed (:status o)) (unpaid? o) (pos? (:total o))))
(refine Paid      [o Order] (and (= :paid (:status o)) (paid-in-full? o) (zero? (:refunded o))))
(refine Shipped   [o Order] (and (= :shipped (:status o)) (paid-in-full? o) (zero? (:refunded o))))
(refine Delivered [o Order] (and (= :delivered (:status o)) (paid-in-full? o)))
(refine Cancelled [o Order] (and (= :cancelled (:status o)) (= (:paid o) (:refunded o))))

(ann place   [Order -> Order])
(ann pay     [Order Nat -> Order])
(ann ship    [Order -> Order])
(ann deliver [Order -> Order])
(ann cancel  [Order -> Order])
(ann refund  [Order Nat -> Order])
(ann balance [Order -> Int])

(graph order
  {:start  [:cart {:status :cart :total 30 :paid 0 :refunded 0}]
   :states {:cart Cart, :placed Placed, :paid Paid, :shipped Shipped,
            :delivered Delivered, :cancelled Cancelled}
   :edges  {:cart      {[place]  {:to #{:placed} :when (fn [o] (pos? (:total o)))
                                  :changes [:status]}
                        [cancel] {:to #{:cancelled} :changes [:status]}}
            :placed    {[pay Nat] {:to #{:paid} :when (fn [o amt] (= amt (:total o)))
                                   :changes [:status :paid]}
                        [cancel]  {:to #{:cancelled} :changes [:status]}}
            :paid      {[ship]   {:to #{:shipped} :changes [:status]}
                        [cancel] {:to #{:cancelled} :changes [:status :refunded]}}
            :shipped   {[deliver] {:to #{:delivered} :changes [:status]}}
            :delivered {[refund Nat] {:to #{:delivered}
                                      :when (fn [o amt] (and (pos? amt)
                                                             (<= (+ amt (:refunded o)) (:paid o))))
                                      :changes [:refunded]}}}
   :final  [:delivered :cancelled]
   :never  [[:shipped :cancelled]]})

;; a step taken from a state the graph gives it no edge from changes nothing

(law only-a-cart-is-placed
  (forall [o Order] (=> (not= :cart (:status o)) (= o (place o)))))

(law only-a-placed-order-is-paid
  (forall [o Order, amt Nat] (=> (not= :placed (:status o)) (= o (pay o amt)))))

(law only-a-paid-order-ships
  (forall [o Order] (=> (not= :paid (:status o)) (= o (ship o)))))

(law only-a-shipped-order-is-delivered
  (forall [o Order] (=> (not= :shipped (:status o)) (= o (deliver o)))))

(law a-shipped-delivered-or-cancelled-order-cannot-be-cancelled
  (forall [o Order]
    (=> (contains? #{:shipped :delivered :cancelled} (:status o)) (= o (cancel o)))))

(law only-a-delivered-order-is-refunded
  (forall [o Order, amt Nat] (=> (not= :delivered (:status o)) (= o (refund o amt)))))

;; money

(law paying-records-the-amount
  (forall [o Placed] (= (:total o) (:paid (pay o (:total o))))))

(law cancelling-a-paid-order-refunds-it-all
  (forall [o Paid] (= (:paid o) (:refunded (cancel o)))))

(law a-refund-adds-its-amount
  (forall [o Delivered, amt Nat]
    (=> (and (pos? amt) (<= (+ amt (:refunded o)) (:paid o)))
        (= (+ amt (:refunded o)) (:refunded (refund o amt))))))

(law the-balance-is-what-was-paid-less-refunds
  (forall [o Order] (= (balance o) (- (:paid o) (:refunded o)))))
