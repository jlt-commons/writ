(ns writ.spec-demo.lots-loose-spec
  "Says the lot taken is live and of the sku, and that none expires
  sooner -- not which of two that expire together."
  (:require [writ.spec :refer [spec ann law graph refine]]))

(spec writ.spec-demo.lots {:require :tested})

(refine Lot [l {:id Nat, :sku Nat, :qty Nat, :expires Nat}] true)

(ann next-lot [(Index :id Lot) Nat Nat -> (Opt Nat)])

(graph g {:states {:lots (Index :id Lot), :lot (Opt Nat)} :edges {:lots {[next-lot Nat Nat] #{:lot}}}})

(defn live [lots sku now]
  (filter #(and (= sku (:sku %)) (pos? (:qty %)) (< now (:expires %))) (vals lots)))

(law a-live-lot-is-taken
  (forall [lots (Index :id Lot), sku Nat, now Nat]
    (= (some? (next-lot lots sku now)) (boolean (seq (live lots sku now))))))

(law none-expires-sooner
  (forall [lots (Index :id Lot), sku Nat, now Nat]
    (let [id (next-lot lots sku now)]
      (=> (some? id)
          (and (some #(= id (:id %)) (live lots sku now))
               (every? #(<= (:expires (get lots id)) (:expires %)) (live lots sku now)))))))
