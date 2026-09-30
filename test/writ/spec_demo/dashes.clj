(ns writ.spec-demo.dashes
  "Spaces to dashes, through clojure.string's replace, referred in place
  of clojure.core's."
  (:refer-clojure :exclude [replace])
  (:require [clojure.string :refer [replace]]))

(defn dashes [s] (replace s " " "-"))
