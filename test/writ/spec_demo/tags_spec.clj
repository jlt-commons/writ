(ns writ.spec-demo.tags-spec
  "Laws over a pipeline, by count, by index and whole: each is proved."
  (:require [writ.spec :refer [spec ann law graph refine]]))

(spec writ.spec-demo.tags {:test false :require :proved})

(refine Item [x {:w Nat}] true)
(refine Tagged [x {:w Nat :k Nat}] true)

(ann tag [(Vec Item) -> (Vec Tagged)])

(graph tagging {:states {:items (Vec Item) :tagged (Vec Tagged)} :edges {:items {[tag] #{:tagged}}}})

(law one-tag-per-item (forall [xs (Vec Item)] (= (count xs) (count (tag xs)))))

(law a-tag-is-its-place
  (forall [xs (Vec Item), i Nat] (=> (< i (count xs)) (= i (:k (nth (tag xs) i))))))

(law tagging-keeps-the-weights (forall [xs (Vec Item)] (= (mapv :w xs) (mapv :w (tag xs)))))
