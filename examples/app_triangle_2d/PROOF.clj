(ns app-triangle-2d.PROOF
  "app_triangle_2d: the proofs, and the verifier."
  (:require [app-triangle-2d.main]
            [app-triangle-2d.LAWS]
            [writ.defn :as w]
            [writ.book :as book]))

(w/proof area-refl-refl    area-refl    refl)
(w/proof area-unit-refl    area-unit    refl)
(w/proof triangle-lit-refl triangle-lit refl)

(defn verify []
  (book/check-files
    "app_triangle_2d/main.clj"
    "app_triangle_2d/LAWS.clj"
    "app_triangle_2d/PROOF.clj"))
