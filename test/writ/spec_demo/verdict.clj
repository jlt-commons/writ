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

(defn with-reason
  "m with its :reason set."
  [m r]
  (assoc m :reason r))

(defn reason-of
  "m's :reason, or :none."
  [m]
  (get m :reason :none))

(defn count-tags
  "How many keywords xs holds."
  [xs]
  (if (empty? xs) 0 (+ (if (keyword? (first xs)) 1 0) (count-tags (rest xs)))))

(defn tags
  "The keywords in x when it is a vector, else none."
  [x]
  (if (vector? x) (count-tags x) 0))

(defn kind
  "What kind of constant x is."
  [x]
  (cond (keyword? x) :kw (symbol? x) :sym :else :other))
