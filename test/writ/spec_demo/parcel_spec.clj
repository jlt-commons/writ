(ns writ.spec-demo.parcel-spec
  "States that are a record with a status and amounts that must agree: a
  random record is rarely one, so its values are built to fit."
  (:require [writ.spec :refer [spec ann refine graph law]]))

(spec writ.spec-demo.parcel)

(refine Status [s Keyword] (contains? #{:placed :paid :shipped} s))
(refine Parcel [o {:status Status, :total Nat, :paid Nat, :refunded Nat}]
  (<= (:refunded o) (:paid o)))

(defn unpaid? [o] (and (zero? (:paid o)) (zero? (:refunded o))))
(defn paid-in-full? [o] (and (pos? (:total o)) (= (:paid o) (:total o))))

(refine Placed [o Parcel] (and (= :placed (:status o)) (unpaid? o) (pos? (:total o))))
(refine Paid   [o Parcel] (and (= :paid (:status o)) (paid-in-full? o) (zero? (:refunded o))))
(refine Ticket [t (Tuple Keyword Nat)] (and (= :open (first t)) (pos? (second t))))

(ann pay [Parcel Nat -> Parcel])

(graph parcel
  {:start  [:placed {:status :placed :total 30 :paid 0 :refunded 0}]
   :states {:placed Placed, :paid Paid}
   :edges  {:placed {[pay Nat] {:to #{:paid} :when (fn [o amt] (= amt (:total o)))
                                :changes [:status :paid]}}}
   :final  [:paid]})

(law only-a-placed-parcel-is-paid
  (forall [o Parcel, amt Nat] (=> (not= :placed (:status o)) (= o (pay o amt)))))
