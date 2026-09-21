(ns app-ray-tracer-3d.main
  "app_ray_tracer_3d: the pure part of bend's ray tracer.

  Ported from bend's demos/app_ray_tracer_3d.  The demo shades each pixel and
  writes the frame out.  The frame size and the per-pixel maths are pure; writ
  checks the dot product and the pixel count.  A vector is `V3` or `[:Vec3 x y
  z]`."
  (:require [writ.defn :as w]))

(w/data Vec V3 (Vec3 Nat Nat Nat))

;; dot product of two vectors.
(w/defn dot [a :- Vec b :- Vec] :- Nat
  (w/match a :- Vec
    (V3 0)
    ((Vec3 x y z)
     (w/match b :- Vec
       (V3 0)
       ((Vec3 p q r) (+ (* x p) (+ (* y q) (* z r))))))))

;; how many pixels a width-by-height frame has.
(w/defn render-pixels [w :- Nat h :- Nat] :- Nat
  (* w h))
