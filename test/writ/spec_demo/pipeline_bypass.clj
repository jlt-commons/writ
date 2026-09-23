(ns writ.spec-demo.pipeline-bypass
  "`handle` checks validity itself and builds the response, skipping the
  `respond` layer."
  (:require [clojure.string :as str]))

(defn normalize [s]
  (str/lower-case (str/trim s)))

(defn valid? [s]
  (<= 1 (count s) 8))

(defn respond [s]
  (if (valid? s) [:ok s] [:error s]))

(defn handle [s]
  (let [n (normalize s)]
    (if (valid? n) [:ok n] [:error n])))
