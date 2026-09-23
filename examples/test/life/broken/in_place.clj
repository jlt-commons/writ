(ns life.broken.in-place
  "life.core as it comes out when a generation is updated in place: each
  cell's fate is decided against a world in which some of its neighbours
  have already moved on to the next generation.")

(defn neighbours [cell]
  (let [[x y] cell]
    #{[(dec x) (dec y)] [x (dec y)] [(inc x) (dec y)]
      [(dec x) y] [(inc x) y]
      [(dec x) (inc y)] [x (inc y)] [(inc x) (inc y)]}))

(defn- alive-next? [world cell]
  (let [n (count (filter #(contains? world %) (neighbours cell)))]
    (if (contains? world cell)
      (or (= n 2) (= n 3))
      (= n 3))))

(defn step [world]
  (reduce (fn [w cell] (if (alive-next? w cell) (conj w cell) (disj w cell)))
          world
          (into world (mapcat neighbours world))))
