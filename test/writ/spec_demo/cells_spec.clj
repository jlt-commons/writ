(ns writ.spec-demo.cells-spec
  "The rule, cell by cell, and the plane's symmetry: proved for every
  world, however large."
  (:require [writ.spec :refer [spec ann law graph]]))

(spec writ.spec-demo.cells {:require :proved})

(ann neighbours [(Tuple Int Int) -> (Set (Tuple Int Int))])
(ann step       [(Set (Tuple Int Int)) -> (Set (Tuple Int Int))])

(graph life
  {:states {:cell (Tuple Int Int), :world (Set (Tuple Int Int))}
   :edges  {:cell  {[neighbours] #{:world}}
            :world {[step] #{:world}}}})

(def offsets [[-1 -1] [0 -1] [1 -1] [-1 0] [1 0] [-1 1] [0 1] [1 1]])

(defn around [cell]
  (let [[x y] cell] (map (fn [o] [(+ x (first o)) (+ y (second o))]) offsets)))

(defn touching [world cell] (count (filter (fn [c] (contains? world c)) (around cell))))

(defn alive-by-the-rule? [world cell]
  (let [n (touching world cell)]
    (if (contains? world cell) (or (= n 2) (= n 3)) (= n 3))))

(defn shifted [dx dy world]
  (set (map (fn [c] [(+ (first c) dx) (+ (second c) dy)]) world)))

(law neighbours-are-the-eight-cells-around
  (forall [x Int, y Int] (= (neighbours [x y]) (set (around [x y])))))

(law a-cell-lives-by-the-rule
  (forall [w (Set (Tuple Int Int)), x Int, y Int]
    (= (contains? (step w) [x y]) (alive-by-the-rule? w [x y]))))

(law the-plane-has-no-favoured-place
  (forall [w (Set (Tuple Int Int)), dx Int, dy Int]
    (= (step (shifted dx dy w)) (shifted dx dy (step w)))))

(law a-blinker-turns (= #{[1 0] [1 1] [1 2]} (step #{[0 1] [1 1] [2 1]})))
