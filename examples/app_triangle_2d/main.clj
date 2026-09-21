(ns app-triangle-2d.main
  "app_triangle_2d: the pure part of bend's 2D triangle demo.

  Ported from bend's demos/app_triangle_2d.  The demo works out a triangle's
  on-screen extent from its three points.  No window is needed for the geometry.
  `ox`/`oy` take a point apart, and `area` is twice the bounding box side, the
  quantity the demo scales by.  A point is either the origin `O`, or `[:At x y]`."
  (:require [writ.defn :as w]))

(w/data Pt O (At Nat Nat))

;; the larger of two coordinates.
(w/defn bounds [^:many x :- Nat ^:many y :- Nat] :- Nat
  (if (<= x y) y x))

;; a point's x coordinate.
(w/defn ox [p :- Pt] :- Nat
  (w/match p :- Pt
    (O 0)
    ((At x y) x)))

;; a point's y coordinate.
(w/defn oy [p :- Pt] :- Nat
  (w/match p :- Pt
    (O 0)
    ((At x y) y)))

;; twice the bounding box side of a triangle with legs x and y.
(w/defn area [x :- Nat y :- Nat] :- Nat
  (let [^:many s (bounds x y)] (* 2 (* s s))))
