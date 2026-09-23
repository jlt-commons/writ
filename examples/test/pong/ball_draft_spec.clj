(ns pong.ball-draft-spec
  "A first draft of the ball's laws, kept to show what writ says about it.
  Every law holds for pong.core, and yet the draft never says that the ball
  moves: `advance` could hand back the ball it was given and pass. writ's
  adequacy check tries exactly that stand-in and reports the gap.
  core_spec.clj closes it with `in-open-court-the-ball-travels-at-its-velocity`."
  (:require [pong.core :refer [W H PH LEFT-X]]
            [writ.spec :refer [spec ann law]]))

(spec pong.core)

(ann advance [(Tuple Int Int Int Int) Int Int -> (Tuple Int Int Int Int)])

(defn court-paddle [y] (mod y (inc (- H PH))))

(defn court-ball [x y dx dy]
  (let [s (inc (mod (abs dx) 3))]
    [(mod x W) (mod y H) (if (neg? dx) (- s) s) (- (mod dy 5) 2)]))

(defn under? [paddle-y y] (and (<= paddle-y y) (< y (+ paddle-y PH))))

(defn pace-kept? [[_ _ dx _] [_ y2 dx2 dy2]]
  (and (= (abs dx) (abs dx2)) (<= (abs dy2) 2) (<= 0 y2 (dec H))))

(law the-ball-stays-between-the-walls-at-its-pace
  (forall [x Int, y Int, dx Int, dy Int, ly Int, ry Int]
    (pace-kept? (court-ball x y dx dy)
                (advance (court-ball x y dx dy) (court-paddle ly) (court-paddle ry)))))

(defn held-by-left? [paddle-y _before [x2 y2]]
  (or (> x2 LEFT-X) (not (under? paddle-y y2))))

(law the-left-paddle-stops-the-ball
  (forall [x Int, y Int, dx Int, dy Int, ly Int, ry Int]
    (=> (> (first (court-ball x y dx dy)) LEFT-X)
        (held-by-left? (court-paddle ly) (court-ball x y dx dy)
                       (advance (court-ball x y dx dy) (court-paddle ly) (court-paddle ry))))))
