(ns life.broken.highlife
  "life.fast with a rule that is almost Conway's: a dead cell with six live
  neighbours is born as well as one with three. That is HighLife (B36/S23),
  and most small patterns never show the difference.")

(defn neighbours [cell]
  (let [[x y] cell]
    #{[(dec x) (dec y)] [x (dec y)] [(inc x) (dec y)]
      [(dec x) y] [(inc x) y]
      [(dec x) (inc y)] [x (inc y)] [(inc x) (inc y)]}))

(defn step [world]
  (set (keep (fn [[cell n]]
               (when (or (= n 3) (= n 6) (and (= n 2) (contains? world cell)))
                 cell))
             (frequencies (mapcat neighbours world)))))
