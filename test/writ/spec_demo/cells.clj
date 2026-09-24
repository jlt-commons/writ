(ns writ.spec-demo.cells
  "Conway's rule on an unbounded plane, as a set of live cells.")

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
