(ns writ.spec-demo.pipeline
  "A request handled in layers: normalize the input, then respond, which
  alone decides validity. The spec's `calls` forms pin that layering."
  (:require [clojure.string :as str]))

(defn normalize [s]
  (str/lower-case (str/trim s)))

(defn valid? [s]
  (<= 1 (count s) 8))

(defn respond [s]
  (if (valid? s) [:ok s] [:error s]))

(defn handle [s]
  (respond (normalize s)))
