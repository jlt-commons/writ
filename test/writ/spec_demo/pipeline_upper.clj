(ns writ.spec-demo.pipeline-upper
  "`normalize` shouts: it upper-cases, which the spec says no request
  handling may do."
  (:require [clojure.string :as str]))

(defn normalize [s]
  (str/upper-case (str/trim s)))

(defn valid? [s]
  (<= 1 (count s) 8))

(defn respond [s]
  (if (valid? s) [:ok s] [:error s]))

(defn handle [s]
  (respond (normalize s)))
