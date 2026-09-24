(ns life.core-spec
  "The contract for the Game of Life, for any implementation of it.

  The rule is stated cell by cell: a cell is alive after a step exactly
  when it has three live neighbours, or two and was alive. That is the
  whole meaning of `step`, for every world and every cell, and it is
  proved from the code. So is what the rule implies: the plane has no
  favoured place, and a world shifted and stepped is the world stepped
  and shifted.

  Random worlds are sparse, and a sparse world hardly ever has a cell with
  three live neighbours. `packed` folds a generated world into a 6x6 box,
  and one law, tested on crowded worlds, compares whole generations with
  a model of the rule, so a broken rule is caught with a small world."
  (:require [writ.spec :refer [spec ann refine graph flow law]]))

(spec life.core {:require :proved})

(ann neighbours [(Tuple Int Int) -> (Set (Tuple Int Int))])
(ann step       [(Set (Tuple Int Int)) -> (Set (Tuple Int Int))])

;; --- the states: a world, and the cells around a cell ------------------------------

(refine Neighbourhood [cells (Set (Tuple Int Int))] (= 8 (count cells)))

(graph life
  {:states {:cell (Tuple Int Int), :around Neighbourhood, :world (Set (Tuple Int Int))}
   :edges  {:cell  {[neighbours] #{:around}}
            :world {[step] #{:world}}}})

;; a step looks at the live cells and the cells around them
(flow step [world] [world neighbours :result])

;; --- the rule, cell by cell ------------------------------------------------------

(def offsets [[-1 -1] [0 -1] [1 -1] [-1 0] [1 0] [-1 1] [0 1] [1 1]])

(defn around [cell]
  (let [[x y] cell]
    (map (fn [o] [(+ x (first o)) (+ y (second o))]) offsets)))

(defn touching [world cell]
  (count (filter (fn [c] (contains? world c)) (around cell))))

(defn alive-by-the-rule? [world cell]
  (let [n (touching world cell)]
    (if (contains? world cell) (or (= n 2) (= n 3)) (= n 3))))

(law neighbours-are-the-eight-cells-around
  (forall [x Int, y Int] (= (neighbours [x y]) (set (around [x y])))))

(law neighbours-names-each-once
  (forall [x Int, y Int] (= 8 (count (neighbours [x y])))))

(law a-cell-lives-by-the-rule
  (forall [w (Set (Tuple Int Int)), x Int, y Int]
    (= (contains? (step w) [x y]) (alive-by-the-rule? w [x y]))))

(defn shifted [dx dy world]
  (set (map (fn [c] [(+ (first c) dx) (+ (second c) dy)]) world)))

(law the-plane-has-no-favoured-place
  (forall [w (Set (Tuple Int Int)), dx Int, dy Int]
    (= (step (shifted dx dy w))
       (shifted dx dy (step w)))))

;; --- whole generations, on crowded worlds -----------------------------------------

(defn next-generation [world]
  (if (empty? world)
    #{}
    (let [xs (map first world) ys (map second world)]
      (set (for [x (range (dec (apply min xs)) (+ 2 (apply max xs)))
                 y (range (dec (apply min ys)) (+ 2 (apply max ys)))
                 :when (alive-by-the-rule? world [x y])]
             [x y])))))

(defn packed [world] (set (map (fn [[x y]] [(mod x 6) (mod y 6)]) world)))

(defn follows-the-rule?
  "`world` stepped to `next`, and the rule says it steps to `by-rule`."
  [world next by-rule]
  (= next by-rule))

(law a-generation-follows-the-rule
  {:require :tested
   :because "it samples crowded worlds so its tests reach births and deaths; the rule itself is proved cell by cell in a-cell-lives-by-the-rule"}
  (forall [w (Set (Tuple Int Int))]
    (follows-the-rule? (packed w) (step (packed w)) (next-generation (packed w)))))

;; --- the famous patterns ----------------------------------------------------------

(def block #{[0 0] [1 0] [0 1] [1 1]})
(def blinker #{[0 1] [1 1] [2 1]})
(def glider #{[1 0] [2 1] [0 2] [1 2] [2 2]})

(law a-block-is-still (= block (step block)))

(law a-blinker-turns-and-turns-back
  (and (= #{[1 0] [1 1] [1 2]} (step blinker))
       (= blinker (step (step blinker)))))

(law a-glider-moves-one-cell-diagonally-every-four-generations
  (= (shifted 1 1 glider) (step (step (step (step glider))))))
