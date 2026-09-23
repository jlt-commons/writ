(ns writ.spec-demo.pipeline-shadow
  "`handle` binds a local named `respond`, so it never reaches the
  namespace's `respond`."
  (:require [clojure.string :as str]))

(defn normalize [s]
  (str/lower-case (str/trim s)))

(defn valid? [s]
  (<= 1 (count s) 8))

(defn respond [s]
  (if (valid? s) [:ok s] [:error s]))

(defn handle [s]
  (let [respond (fn [x] (if (valid? x) [:ok x] [:error x]))]
    (respond (normalize s))))
