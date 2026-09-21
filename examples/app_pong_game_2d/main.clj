(ns app-pong-game-2d.main
  "app_pong_game_2d: the pure part of bend's Pong.

  Ported from bend's demos/app_pong_game_2d.  The demo's frame loop reads a quit
  event to decide whether to keep playing, and tracks which way a paddle is
  moving, the last key pressed winning.  Neither needs a window; both are pure
  folds.  `quits` scans a run of events for a quit, and `holds` folds a list of
  key states with the last one winning."
  (:require [writ.defn :as w]))

;; key states: true is down.
(w/data Keys KNil (KCons Bool Keys))

;; an input event.
(w/data Ev Tick Esc Quit)

;; a run of events.
(w/data Evs Nil (Cons Ev Evs))

;; an event that ends the game.
(w/defn quit? [e :- Ev] :- Bool
  (w/match e :- Ev
    (Tick false)
    (Esc true)
    (Quit true)))

;; whether a run of events contains a quit.
(w/defn ^{:writ/descend true} quits [evs :- Evs] :- Bool
  (w/match evs :- Evs
    (Nil false)
    ((Cons e t) (if (quit? e) true (quits t)))))

;; the paddle's direction after a run of presses: the last press wins.
(w/defn ^{:writ/descend true} holds [ks :- Keys acc :- Bool] :- Bool
  (w/match ks :- Keys
    (KNil acc)
    ((KCons p t) (holds t p))))
