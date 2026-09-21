(ns app-win-is-bug-2d.main
  "app_win_is_bug_2d: the pure part of bend's Win Is Bug.

  Ported from bend's demos/app_win_is_bug_2d.  The demo runs a cellular
  automaton: each cell is dead or alive, and a generation is a list of cells.
  writ checks the cell rule and the population count.  A list is `:Nil` or
  `[:Cons c t]`."
  (:require [writ.defn :as w]))

(w/data Cell Dead Alive)
(w/data Cells Nil (Cons Cell Cells))

;; 1 when the cell is alive, 0 when dead.
(w/defn alive? [c :- Cell] :- Nat
  (w/match c :- Cell
    (Dead 0)
    (Alive 1)))

;; how many cells in a generation are alive.
(w/defn ^{:writ/descend true} population [cs :- Cells] :- Nat
  (w/match cs :- Cells
    (Nil 0)
    ((Cons c t) (+ (alive? c) (population t)))))

;; run n generations; the demo counts the ticks it has seen.
(w/defn ^{:writ/descend true} ticks [^:many n :- Nat] :- Nat
  (if (zero? n) 0 (inc (ticks (dec n)))))
