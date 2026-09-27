(ns writ.spec-demo.verdict
  "A pure core that calls into another pure namespace, over values of any
  type, and takes a fn argument."
  (:require [writ.spec-demo.verdict-core :as core]))

(defn restart?
  "Does a child of kind exiting with reason earn a restart?"
  [kind reason]
  (cond
    (= :temporary kind) false
    (= :transient kind) (not (core/orderly? reason))
    :else true))

(defn keep-if [xs ok?] (vec (filter ok? xs)))

(defn payload
  "The value in an [:ok value] vector, else :bad -- a list is not one."
  [ret]
  (if (and (vector? ret) (= 2 (count ret)) (= :ok (first ret))) (get ret 1) :bad))
