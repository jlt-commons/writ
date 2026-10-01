(ns writ.spec-demo.waitlist
  "A queue of members per title, each in it at most once.")

(defn- queue [w t] (get w t []))

(defn join [w t m]
  (if (some #{m} (queue w t))
    w
    (assoc w t (conj (vec (queue w t)) m))))

(defn serve [w t]
  (if (seq (queue w t))
    (assoc w t (vec (rest (queue w t))))
    w))

(defn next-up [w t]
  (first (queue w t)))

(defn cancel [w t m]
  (if (some #{m} (queue w t))
    (assoc w t (vec (remove #{m} (queue w t))))
    w))
