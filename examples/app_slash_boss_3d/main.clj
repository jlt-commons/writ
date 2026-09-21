(ns app-slash-boss-3d.main
  "app_slash_boss_3d: the pure part of bend's Slash Boss.

  Ported from bend's demos/app_slash_boss_3d.  The demo moves the boss and
  watches for a quit.  Both are pure: `move-right`/`move-up` shift a position by
  one, and `quit?` reads an event.  A position is `Origin` or `[:Pos3 x y z]`."
  (:require [writ.defn :as w]))

(w/data Pos Origin (Pos3 Nat Nat Nat))

(w/defn move-right [p :- Pos] :- Pos
  (w/match p :- Pos
    (Origin [:Pos3 1 0 0])
    ((Pos3 x y z) [:Pos3 (inc x) y z])))

(w/defn move-up [p :- Pos] :- Pos
  (w/match p :- Pos
    (Origin [:Pos3 0 1 0])
    ((Pos3 x y z) [:Pos3 x (inc y) z])))

(w/data Ev Tick Esc Quit)

(w/defn quit? [e :- Ev] :- Bool
  (w/match e :- Ev
    (Tick false)
    (Esc true)
    (Quit true)))
