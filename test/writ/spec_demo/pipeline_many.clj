(ns writ.spec-demo.pipeline-many
  "Requests handled in bulk: data reaches each layer through a lambda, a
  fn passed by name, a loop and a let."
  (:require [clojure.string :as str]))

(defn normalize [s]
  (str/lower-case (str/trim s)))

(defn valid? [s]
  (<= 1 (count s) 8))

(defn respond [s]
  (if (valid? s) [:ok s] [:error s]))

(defn handle-all [ss]
  (map respond (map (fn [s] (normalize s)) ss)))

(defn count-ok [ss]
  (loop [xs ss, n 0]
    (if (seq xs)
      (let [r (respond (first xs))]
        (recur (rest xs) (if (= :ok (first r)) (inc n) n)))
      n)))
