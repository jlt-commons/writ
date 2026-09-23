(ns writ.spec-demo.pipeline-inline
  "`handle` inlines the normalisation instead of calling `normalize`. It
  behaves the same today, and drifts the day `normalize` changes."
  (:require [clojure.string :as str]))

(defn normalize [s]
  (str/lower-case (str/trim s)))

(defn valid? [s]
  (<= 1 (count s) 8))

(defn respond [s]
  (if (valid? s) [:ok s] [:error s]))

(defn handle [s]
  (respond (str/lower-case (str/trim s))))
