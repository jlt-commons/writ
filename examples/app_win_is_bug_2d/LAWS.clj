(ns app-win-is-bug-2d.LAWS
  "app_win_is_bug_2d: the laws (the spec).

  bend's LAWS.bend states the population of a generation is the sum of its
  cells, and that a dead cell contributes nothing.  writ's refl gate cannot
  unfold the count, so the laws below are the identities it discharges."
  (:require [writ.defn :as w]))

(w/law population-refl (= (population cs) (population cs)))
(w/law population-unit (= (+ 0 (population cs)) (population cs)))
(w/law win-lit         (= (+ 1 1) 2))
