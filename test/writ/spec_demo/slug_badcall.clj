(ns writ.spec-demo.slug-badcall
  "clean hands trim a number."
  (:require [clojure.string :as str]))

(defn clean [s]
  (str/lower-case (str/trim (count s))))

(defn same-slug? [a b]
  (= (clean a) (clean b)))
