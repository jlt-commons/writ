(ns app-ray-tracer-3d.PROOF
  "app_ray_tracer_3d: the proofs, and the verifier."
  (:require [app-ray-tracer-3d.main]
            [app-ray-tracer-3d.LAWS]
            [writ.defn :as w]
            [writ.book :as book]))

(w/proof dot-refl-refl    dot-refl    refl)
(w/proof render-unit-refl render-unit refl)
(w/proof ray-lit-refl     ray-lit     refl)

(defn verify []
  (book/check-files
    "app_ray_tracer_3d/main.clj"
    "app_ray_tracer_3d/LAWS.clj"
    "app_ray_tracer_3d/PROOF.clj"))
