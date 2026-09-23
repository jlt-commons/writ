(ns life.core-spec
  "The contract for the Game of Life, for any implementation of it.

  The rule is stated once, cell by cell, in `next-generation`: a model that
  scans every cell of the box around the world. It is slow and plain, and
  it only runs here. The laws say the code agrees with it, and they add
  what the rule implies: the plane has no favoured place, and the famous
  patterns behave as they should.

  Random worlds are sparse, and a sparse world hardly ever has a cell with
  three live neighbours. `packed` folds any generated world into a 6x6
  box, so every trial is crowded enough to exercise the rule."
  (:require [writ.spec :refer [spec ann law]]))

(spec life.core)

(ann neighbours [(Tuple Int Int) -> (Set (Tuple Int Int))])
(ann step       [(Set (Tuple Int Int)) -> (Set (Tuple Int Int))])

;; --- the rule, cell by cell --------------------------------------------------------

(defn touching [world x y]
  (count (for [dx [-1 0 1] dy [-1 0 1]
               :when (and (not= 0 dx dy) (contains? world [(+ x dx) (+ y dy)]))]
           1)))

(defn next-generation [world]
  (if (empty? world)
    #{}
    (let [xs (map first world) ys (map second world)]
      (set (for [x (range (dec (apply min xs)) (+ 2 (apply max xs)))
                 y (range (dec (apply min ys)) (+ 2 (apply max ys)))
                 :let [n (touching world x y)]
                 :when (if (contains? world [x y]) (<= 2 n 3) (= n 3))]
             [x y])))))

(defn packed [world] (set (map (fn [[x y]] [(mod x 6) (mod y 6)]) world)))

(defn shifted [dx dy world] (set (map (fn [[x y]] [(+ x dx) (+ y dy)]) world)))

;; --- laws ------------------------------------------------------------------------

(law neighbours-are-the-eight-cells-around
  (forall [x Int, y Int]
    (= (neighbours [x y])
       (set (for [dx [-1 0 1] dy [-1 0 1] :when (not= 0 dx dy)] [(+ x dx) (+ y dy)])))))

(law neighbours-names-each-once
  (forall [x Int, y Int] (= 8 (count (neighbours [x y])))))

(defn follows-the-rule?
  "`world` stepped to `next`, and the rule says it steps to `by-rule`."
  [world next by-rule]
  (= next by-rule))

(law a-generation-follows-the-rule
  (forall [w (Set (Tuple Int Int))]
    (follows-the-rule? (packed w) (step (packed w)) (next-generation (packed w)))))

(law the-plane-has-no-favoured-place
  (forall [w (Set (Tuple Int Int)), dx Int, dy Int]
    (= (step (shifted dx dy (packed w)))
       (shifted dx dy (step (packed w))))))

(def block #{[0 0] [1 0] [0 1] [1 1]})
(def blinker #{[0 1] [1 1] [2 1]})
(def glider #{[1 0] [2 1] [0 2] [1 2] [2 2]})

(law a-block-is-still (= block (step block)))

(law a-blinker-turns-and-turns-back
  (and (= #{[1 0] [1 1] [1 2]} (step blinker))
       (= blinker (step (step blinker)))))

(law a-glider-moves-one-cell-diagonally-every-four-generations
  (= (shifted 1 1 glider) (step (step (step (step glider))))))
