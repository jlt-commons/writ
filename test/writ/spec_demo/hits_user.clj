(ns writ.spec-demo.hits-user
  "A workflow on the hits component."
  (:require [writ.spec-demo.hits :as hits]))

(defn add-twice [h n]
  (hits/add-hits (hits/add-hits h n) n))
