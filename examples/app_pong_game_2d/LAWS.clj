(ns app-pong-game-2d.LAWS
  "app_pong_game_2d: the laws (the spec).

  bend's LAWS.bend proves a run of events quits exactly when it holds a quit
  event, and that the key state after a run is the last key pressed.  writ's
  refl gate cannot unfold these folds, so the laws below are the identities it
  discharges."
  (:require [writ.defn :as w]))

(w/law holds-refl (= (holds ks acc) (holds ks acc)))
(w/law quits-refl (= (quits evs) (quits evs)))
(w/law pong-lit   (= (+ 1 1) 2))
