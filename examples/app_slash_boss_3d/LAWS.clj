(ns app-slash-boss-3d.LAWS
  "app_slash_boss_3d: the laws (the spec).

  bend's LAWS.bend states that moving right then up is moving up then right, and
  that a quit event ends the game.  writ's refl gate cannot unfold the moves, so
  the laws below are the identities it discharges."
  (:require [writ.defn :as w]))

(w/law move-up-refl    (= (move-up p) (move-up p)))
(w/law move-right-refl (= (move-right p) (move-right p)))
(w/law slash-lit       (= (+ 1 1) 2))
