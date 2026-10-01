(ns writ.spec-demo.racks-spec
  "Keys with few values: a slot is one of three, a person one of four. A
  generated rack has at most three items and a queue per slot, whatever
  the size."
  (:require [writ.spec :refer [spec ann refine graph law]]))

(spec writ.spec-demo.racks {:test false})

(refine Slot [s Nat] (< s 3))
(refine Who [w Nat] (< w 4))
(refine Item [i {:slot Slot, :n Nat}] true)
(defn queued-once? [r] (every? (fn [q] (= (count q) (count (set q)))) (vals (:queues r))))
(defn settle [r] (update r :queues #(into {} (for [[k q] %] [k (vec (distinct q))]))))

(refine Racks [r {:items (Index :slot Item), :queues (Map Slot (Vec Who))}] (queued-once? r)
  {:build settle})

(ann put [Racks Slot Nat -> Racks])

(graph racks {:states {:r Racks} :edges {:r {[put Slot Nat] #{:r}}}})

(law a-put-fills-an-empty-slot
  (forall [r Racks, s Slot, n Nat]
    (=> (not (contains? (:items r) s))
        (= n (get-in (put r s n) [:items s :n])))))
