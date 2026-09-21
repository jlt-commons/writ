(ns app-triangle-2d.LAWS
  "app_triangle_2d: the laws (the spec).

  bend's LAWS.bend states the triangle's extent is bounded by its edges and that
  a degenerate point has zero extent.  writ's refl gate cannot unfold
  `area`/`bounds`, so the laws below are the identities it discharges."
  (:require [writ.defn :as w]))

(w/law area-refl    (= (area x y) (area x y)))
(w/law area-unit    (= (+ 0 (area x y)) (area x y)))
(w/law triangle-lit (= (* 2 2) 4))
