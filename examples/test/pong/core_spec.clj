(ns pong.core-spec
  "The contract for pong.core: what pong is, stated for every position on
  the court rather than for a few rallies.

  Generated Ints fall anywhere, so the laws build their games through
  `court-ball`, `court-paddle` and `game-of`, which fold any Int onto the
  court. Every trial is then a position the game can really be in, and no
  `=>` premise starves for lack of inputs."
  (:require [pong.core :refer [W H PH LEFT-X RIGHT-X WIN]]
            [writ.spec :refer [spec data ann law]]))

(spec pong.core)

(data Side Left Right)
(data Phase (Serving Nat) Playing Paused (Won Side))
(data Key Idle Up Down Pause)

(ann move-paddle [Int Key -> Int])
(ann track       [Int Int -> Int])
(ann advance     [(Tuple Int Int Int Int) Int Int -> (Tuple Int Int Int Int)])
(ann serve       [Side -> (Tuple Int Int Int Int)])
(ann new-game    [-> (Tuple Phase (Tuple Int Int Int Int) Int Int Nat Nat)])
(ann play        [(Tuple Int Int Int Int) Int Int Nat Nat Key
                  -> (Tuple Phase (Tuple Int Int Int Int) Int Int Nat Nat)])
(ann step        [(Tuple Phase (Tuple Int Int Int Int) Int Int Nat Nat) Key
                  -> (Tuple Phase (Tuple Int Int Int Int) Int Int Nat Nat)])

;; --- the court, in the spec's own terms --------------------------------------

(defn court-paddle [y] (mod y (inc (- H PH))))

(defn court-ball
  "A ball on the court: across by 1 to 3 cells a tick, up or down by at most 2."
  [x y dx dy]
  (let [s (inc (mod (abs dx) 3))]
    [(mod x W) (mod y H) (if (neg? dx) (- s) s) (- (mod dy 5) 2)]))

(defn game-of [phase x y dx dy ly ry ls rs]
  [phase (court-ball x y dx dy) (court-paddle ly) (court-paddle ry) (mod ls WIN) (mod rs WIN)])

(defn paddle-ok? [y] (<= 0 y (- H PH)))

(defn under? [paddle-y y] (and (<= paddle-y y) (< y (+ paddle-y PH))))

(defn on-court? [[x y dx dy]]
  (and (<= 0 x (dec W)) (<= 0 y (dec H)) (<= 1 (abs dx) 3) (<= (abs dy) 2)))

(defn valid-game? [[phase ball ly ry ls rs]]
  (and (paddle-ok? ly) (paddle-ok? ry) (<= ls WIN) (<= rs WIN)
       (or (= :Won (first phase)) (on-court? ball))))

(defn phase-of [game] (first (first game)))
(defn scores [game] (drop 4 game))

;; --- paddles -------------------------------------------------------------------

(law a-paddle-never-leaves-the-court
  (forall [y Int, k Key] (paddle-ok? (move-paddle y k))))

(law up-and-down-move-two-rows-to-the-wall
  (forall [y Int]
    (and (= (move-paddle (court-paddle y) [:Up]) (max 0 (- (court-paddle y) 2)))
         (= (move-paddle (court-paddle y) [:Down]) (min (- H PH) (+ (court-paddle y) 2)))
         (= (move-paddle (court-paddle y) [:Idle]) (court-paddle y)))))

(defn closer-by-one? [p p2 ball-y]
  (let [gap (fn [q] (abs (- (+ q (quot PH 2)) ball-y)))]
    (and (paddle-ok? p2) (<= (abs (- p2 p)) 1)
         (<= (gap p2) (gap p))
         (or (zero? (gap p)) (not (< 0 p (- H PH))) (< (gap p2) (gap p))))))

(law the-cpu-paddle-closes-on-the-ball
  (forall [y Int, by Int]
    (closer-by-one? (court-paddle y) (track (court-paddle y) (mod by H)) (mod by H))))

;; --- the ball --------------------------------------------------------------------

(defn pace-kept? [[_ _ dx _] [_ y2 dx2 dy2]]
  (and (= (abs dx) (abs dx2)) (<= (abs dy2) 2) (<= 0 y2 (dec H))))

(law the-ball-stays-between-the-walls-at-its-pace
  (forall [x Int, y Int, dx Int, dy Int, ly Int, ry Int]
    (pace-kept? (court-ball x y dx dy)
                (advance (court-ball x y dx dy) (court-paddle ly) (court-paddle ry)))))

(defn open-court? [[x y dx dy]]
  (and (< (+ LEFT-X 3) x (- RIGHT-X 3)) (< 2 y (- H 3))))

(law in-open-court-the-ball-travels-at-its-velocity
  (forall [x Int, y Int, dx Int, dy Int, ly Int, ry Int]
    (=> (open-court? (court-ball x y dx dy))
        (= (advance (court-ball x y dx dy) (court-paddle ly) (court-paddle ry))
           (let [[x y dx dy] (court-ball x y dx dy)] [(+ x dx) (+ y dy) dx dy])))))

;; A paddle is a wall on its own rows: a ball in front of it is still in
;; front after a tick, unless it went by on a row the paddle does not cover.
;; However fast the ball, it cannot jump the paddle.
(defn held-by-left? [paddle-y _before [x2 y2]]
  (or (> x2 LEFT-X) (not (under? paddle-y y2))))

(law the-left-paddle-stops-the-ball
  (forall [x Int, y Int, dx Int, dy Int, ly Int, ry Int]
    (=> (> (first (court-ball x y dx dy)) LEFT-X)
        (held-by-left? (court-paddle ly) (court-ball x y dx dy)
                       (advance (court-ball x y dx dy) (court-paddle ly) (court-paddle ry))))))

(defn held-by-right? [paddle-y _before [x2 y2]]
  (or (< x2 RIGHT-X) (not (under? paddle-y y2))))

(law the-right-paddle-stops-the-ball
  (forall [x Int, y Int, dx Int, dy Int, ly Int, ry Int]
    (=> (< (first (court-ball x y dx dy)) RIGHT-X)
        (held-by-right? (court-paddle ry) (court-ball x y dx dy)
                        (advance (court-ball x y dx dy) (court-paddle ly) (court-paddle ry))))))

(law a-serve-goes-to-the-side-named
  (and (neg? (nth (serve [:Left]) 2)) (pos? (nth (serve [:Right]) 2))
       (on-court? (serve [:Left])) (on-court? (serve [:Right]))))

;; --- the game --------------------------------------------------------------------

(law a-game-starts-level-and-serving
  (and (= [0 0] (scores (new-game))) (= :Serving (phase-of (new-game)))
       (valid-game? (new-game))))

(law every-tick-leaves-a-game-that-can-be
  (forall [p Phase, x Int, y Int, dx Int, dy Int, ly Int, ry Int, ls Nat, rs Nat, k Key]
    (valid-game? (step (game-of p x y dx dy ly ry ls rs) k))))

(defn one-point-at-most? [[a b] [a2 b2]]
  (and (<= a a2) (<= b b2) (<= (+ a2 b2) (inc (+ a b)))))

(law a-tick-scores-at-most-one-point
  (forall [p Phase, x Int, y Int, dx Int, dy Int, ly Int, ry Int, ls Nat, rs Nat, k Key]
    (=> (not= :Won (first p))
        (one-point-at-most? (scores (game-of p x y dx dy ly ry ls rs))
                            (scores (step (game-of p x y dx dy ly ry ls rs) k))))))

(law the-game-is-won-exactly-at-WIN
  (forall [p Phase, x Int, y Int, dx Int, dy Int, ly Int, ry Int, ls Nat, rs Nat, k Key]
    (=> (not= :Won (first p))
        (= (= :Won (phase-of (step (game-of p x y dx dy ly ry ls rs) k)))
           (boolean (some #(>= % WIN) (scores (step (game-of p x y dx dy ly ry ls rs) k))))))))

(law pausing-twice-changes-nothing
  (forall [x Int, y Int, dx Int, dy Int, ly Int, ry Int, ls Nat, rs Nat]
    (= (step (step (game-of [:Playing] x y dx dy ly ry ls rs) [:Pause]) [:Pause])
       (game-of [:Playing] x y dx dy ly ry ls rs))))

(law a-paused-game-stands-still
  (forall [x Int, y Int, dx Int, dy Int, ly Int, ry Int, ls Nat, rs Nat, k Key]
    (=> (not= :Pause (first k))
        (= (step (game-of [:Paused] x y dx dy ly ry ls rs) k)
           (game-of [:Paused] x y dx dy ly ry ls rs)))))

(law a-serve-counts-down
  (forall [n Nat, x Int, y Int, dx Int, dy Int, ly Int, ry Int, ls Nat, rs Nat, k Key]
    (=> (not= :Pause (first k))
        (= (phase-of (step (game-of [:Serving n] x y dx dy ly ry ls rs) k))
           (if (pos? n) :Serving :Playing)))))

(law pause-after-a-win-starts-over
  (forall [s Side, x Int, y Int, dx Int, dy Int, ly Int, ry Int, ls Nat, rs Nat]
    (= (step (game-of [:Won s] x y dx dy ly ry ls rs) [:Pause]) (new-game))))
