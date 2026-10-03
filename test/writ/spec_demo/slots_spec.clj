(ns writ.spec-demo.slots-spec
  "A rule across the records of an index: no two slots at once. Random
  indexes of slots nearly always break it, so its values are built a
  slot at a time rather than filtered for."
  (:require [writ.spec :refer [spec ann refine graph law]]))

(spec writ.spec-demo.slots {:test false})

(refine Slot [s {:id Nat, :start Nat, :end Nat}] true)

(defn clash? [a b]
  (and (not= (:id a) (:id b))
       (some #(and (<= (:start a) %) (< % (:end a))) (range (:start b) (:end b)))))

(defn apart? [day]
  (and (every? (fn [[k s]] (and (= k (:id s)) (< (:start s) (:end s)))) day)
       (not-any? (fn [[a b]] (clash? a b)) (for [a (vals day) b (vals day)] [a b]))))

(refine Day [d (Index :id Slot)] (apart? d))

(ann add [Day Slot -> Day])

(graph day {:states {:day Day} :edges {:day {[add Slot] #{:day}}}})

(law a-free-slot-is-added
  (forall [d Day, s Slot]
    (=> (and (< (:start s) (:end s)) (not (contains? d (:id s)))
             (not-any? #(clash? s %) (vals d)))
        (= (add d s) (assoc d (:id s) s)))))
