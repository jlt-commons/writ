(ns writ.spec-demo.lots-spec
  "One law, over any lots, sku and time: it names the tie-break, but a
  random trial seldom makes two live lots of the sku expire together."
  (:require [writ.spec :refer [spec ann law graph refine]]))

(spec writ.spec-demo.lots {:require :tested})

(refine Lot [l {:id Nat, :sku Nat, :qty Nat, :expires Nat}] true)

(ann next-lot [(Index :id Lot) Nat Nat -> (Opt Nat)])

(graph g {:states {:lots (Index :id Lot), :lot (Opt Nat)} :edges {:lots {[next-lot Nat Nat] #{:lot}}}})

(defn live [lots sku now]
  (filter #(and (= sku (:sku %)) (pos? (:qty %)) (< now (:expires %))) (vals lots)))

(law the-earliest-then-the-lowest-id
  (forall [lots (Index :id Lot), sku Nat, now Nat]
    (= (next-lot lots sku now)
       (:id (first (sort-by (fn [l] [(:expires l) (:id l)]) (live lots sku now)))))))
