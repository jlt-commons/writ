(ns writ.spec-demo.twolist-spec
  "The two-vector queue said through a model: its items in order, as one
  vector. Each step must do to the view what the model's step does: one
  law per edge, generated from :model."
  (:require [writ.spec :refer [spec ann graph]]))

(spec writ.spec-demo.twolist {:test false})

(ann enqueue [{:front (Vec Nat), :back (Vec Nat)} Nat -> {:front (Vec Nat), :back (Vec Nat)}])
(ann dequeue [{:front (Vec Nat), :back (Vec Nat)} -> {:front (Vec Nat), :back (Vec Nat)}])

(defn items [q] (into (vec (:front q)) (:back q)))
(defn put [m x] (conj m x))
(defn take-one [m] (vec (rest m)))

(graph queue
  {:states {:q {:front (Vec Nat), :back (Vec Nat)}}
   :edges  {:q {[enqueue Nat] #{:q}
                [dequeue] #{:q}}}
   :model  {:view items :steps {enqueue put, dequeue take-one}}})
