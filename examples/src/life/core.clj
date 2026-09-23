(ns life.core
  "Conway's Game of Life on an unbounded plane. A world is the set of its
  live cells, each [x y]. Written to be read: every cell that could be
  alive next is tested against the rule.")

(defn neighbours [cell]
  (let [[x y] cell]
    #{[(dec x) (dec y)] [x (dec y)] [(inc x) (dec y)]
      [(dec x) y] [(inc x) y]
      [(dec x) (inc y)] [x (inc y)] [(inc x) (inc y)]}))

(defn- live-neighbours [world cell]
  (count (filter #(contains? world %) (neighbours cell))))

(defn- alive-next? [world cell]
  (let [n (live-neighbours world cell)]
    (if (contains? world cell)
      (or (= n 2) (= n 3))
      (= n 3))))

(defn step [world]
  (set (filter #(alive-next? world %)
               (into world (mapcat neighbours world)))))
