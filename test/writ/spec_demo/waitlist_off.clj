(ns writ.spec-demo.waitlist-off
  "The waitlist, wrong: joining twice queues twice, serving drops the last
  in line, and cancelling drops everyone after the member too.")

(defn- queue [w t] (get w t []))

(defn join [w t m]
  (assoc w t (conj (vec (queue w t)) m)))

(defn serve [w t]
  (if (seq (queue w t))
    (assoc w t (vec (butlast (queue w t))))
    w))

(defn next-up [w t]
  (first (queue w t)))

(defn cancel [w t m]
  (if (some #{m} (queue w t))
    (assoc w t (vec (take-while #(not= m %) (queue w t))))
    w))
