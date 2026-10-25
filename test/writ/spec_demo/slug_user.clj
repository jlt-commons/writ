(ns writ.spec-demo.slug-user
  (:require [writ.spec-demo.slug :as slug]))

(defn answer [s]
  (slug/clean s))
