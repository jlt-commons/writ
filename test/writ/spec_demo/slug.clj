(ns writ.spec-demo.slug
  "Slugs: a string trimmed and lower-cased, through clojure.string, which
  writ does not check."
  (:require [clojure.string :as str]))

(defn clean [s]
  (str/lower-case (str/trim s)))

(defn same-slug? [a b]
  (= (clean a) (clean b)))
