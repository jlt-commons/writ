(ns bucket.core
  "A token-bucket rate limiter over integer millisecond timestamps.")

(def capacity 10)
(def interval-ms 100)

(defn refill [b now]
  (let [{:keys [tokens last]} b]
    (if (<= now last)
      b
      (let [k (quot (- now last) interval-ms)]
        (if (>= (+ tokens k) capacity)
          {:tokens capacity :last now}
          {:tokens (+ tokens k) :last (+ last (* k interval-ms))})))))

(defn try-take [b now n]
  (let [r (refill b now)]
    (if (<= n (:tokens r))
      [true (assoc r :tokens (- (:tokens r) n))]
      [false r])))

(defn wait-ms [b now n]
  (let [r (refill b now)]
    (cond
      (> n capacity) nil
      (<= n (:tokens r)) 0
      :else (- (+ (:last r) (* (- n (:tokens r)) interval-ms)) now))))
