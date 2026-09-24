(ns writ.spec-demo.pipeline-swapped
  "`handle` calls both layers, as the spec's `calls` says, but hands
  `respond` the raw input and throws the normalized one away."
  (:require [clojure.string :as str]))

(defn normalize [s]
  (str/lower-case (str/trim s)))

(defn valid? [s]
  (<= 1 (count s) 8))

(defn respond [s]
  (if (valid? s) [:ok s] [:error s]))

(defn handle [s]
  (let [n (normalize s)]
    (respond s)))
