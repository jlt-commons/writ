(ns orders.core
  "An order's life: cart, placed, paid, shipped, delivered, or cancelled.")

(defn place [o]
  (if (and (= :cart (:status o)) (pos? (:total o)))
    (assoc o :status :placed)
    o))

(defn pay [o amount]
  (if (and (= :placed (:status o)) (= amount (:total o)))
    (assoc o :status :paid :paid amount)
    o))

(defn ship [o]
  (if (= :paid (:status o)) (assoc o :status :shipped) o))

(defn deliver [o]
  (if (= :shipped (:status o)) (assoc o :status :delivered) o))

(defn cancel [o]
  (if (contains? #{:cart :placed :paid} (:status o))
    (assoc o :status :cancelled :refunded (:paid o))
    o))

(defn refund [o amount]
  (if (and (= :delivered (:status o))
           (pos? amount)
           (<= (+ (:refunded o) amount) (:paid o)))
    (assoc o :refunded (+ (:refunded o) amount))
    o))

(defn balance [o]
  (- (:paid o) (:refunded o)))
