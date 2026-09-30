(ns writ.spec-demo.slots
  "Slots of a day, none two at once: a slot is added only when it is free.")

(defn- at-once? [a b]
  (< (max (:start a) (:start b)) (min (:end a) (:end b))))

(defn add [day s]
  (if (and (< (:start s) (:end s))
           (not (contains? day (:id s)))
           (not-any? #(at-once? s %) (vals day)))
    (assoc day (:id s) s)
    day))
