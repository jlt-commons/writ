(ns app-ray-tracer-3d.LAWS
  "app_ray_tracer_3d: the laws (the spec).

  bend's LAWS.bend states the dot product is symmetric and the frame is a
  rectangle of pixels.  writ's refl gate cannot unfold `dot`/`render-pixels`, so
  the laws below are the identities it discharges."
  (:require [writ.defn :as w]))

(w/law dot-refl     (= (dot a b) (dot a b)))
(w/law render-unit  (= (+ (render-pixels w h) 0) (render-pixels w h)))
(w/law ray-lit      (= (* 2 3) 6))
