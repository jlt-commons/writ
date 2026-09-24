(ns pong.core-spec
  "The contract for pong.core: its state graph, and what each step means.

  A game is [phase ball left-y right-y left-score right-score]. Its parts
  are refinements -- a Paddle is a row a paddle can be on, a Ball one on
  the court at a pace it can have -- so every generated game is one the
  game can be in, and the prover assumes as much. The graph's states are
  the four phases of a game; each edge is proved from the code, so every
  run of `step` stays inside the graph and keeps its rules."
  (:require [pong.core :refer [W H PH LEFT-X RIGHT-X WIN]]
            [writ.spec :refer [spec data ann refine graph flow law]]))

(spec pong.core {:require :proved})

(data Side Left Right)
(data Phase (Serving Nat) Playing Paused (Won Side))
(data Key Idle Up Down Pause)

;; --- the parts of a game ---------------------------------------------------------

(refine Paddle [y Int] (<= 0 y (- H PH)))
(refine Row    [y Int] (<= 0 y (dec H)))
(refine Column [x Int] (<= 0 x (dec W)))
(refine Pace   [dx Int] (<= 1 (abs dx) 3))
(refine Spin   [dy Int] (<= -2 dy 2))
(refine Ball   [b (Tuple Column Row Pace Spin)] true)
(refine Score  [s Nat] (< s WIN))

(ann move-paddle [Int Key -> Int])
(ann track       [Int Int -> Int])
(ann advance     [(Tuple Int Int Int Int) Int Int -> (Tuple Int Int Int Int)])
(ann serve       [Side -> (Tuple Int Int Int Int)])
(ann new-game    [-> (Tuple Phase (Tuple Int Int Int Int) Int Int Nat Nat)])
(ann play        [(Tuple Int Int Int Int) Int Int Nat Nat Key
                  -> (Tuple Phase (Tuple Int Int Int Int) Int Int Nat Nat)])
(ann step        [(Tuple Phase (Tuple Int Int Int Int) Int Int Nat Nat) Key
                  -> (Tuple Phase (Tuple Int Int Int Int) Int Int Nat Nat)])

;; --- the game's states -----------------------------------------------------------

(defn phase-of [game] (first (first game)))

(defn scores [game] (let [[_ _ _ _ ls rs] game] [ls rs]))

(refine Live [g (Tuple Phase Ball Paddle Paddle Score Score)] (not= :Won (phase-of g)))

(refine Serving [g Live] (= :Serving (phase-of g)))
(refine Playing [g Live] (= :Playing (phase-of g)))
(refine Paused  [g Live] (= :Paused (phase-of g)))
(refine Won     [g (Tuple Phase (Tuple Int Int Int Int) Paddle Paddle Nat Nat)]
  (let [[phase _ _ _ ls rs] g]
    (and (= :Won (first phase)) (<= ls WIN) (<= rs WIN) (or (= ls WIN) (= rs WIN)))))

(graph pong
  {:start  [:serving (new-game)]
   :states {:serving Serving, :playing Playing, :paused Paused, :won Won}
   :edges  {:serving {[step Key] #{:serving :playing :paused}}
            :playing {[step Key] #{:playing :paused :serving :won}}
            :paused  {[step Key] #{:paused :playing}}
            :won     {[step Key] #{:won :serving}}}
   :before [[:playing :won]]})

;; a tick of play: the key moves the left paddle, the ball draws the
;; right one, and the ball moves against both
(flow play [ball ly ry ls rs key]
  [key move-paddle advance :result]
  [ball track advance]
  [ball advance :result])

;; step hands the game and the key to play, and moves the paddle while
;; a serve counts down
(flow step [game key]
  [game play :result]
  [key play]
  [key move-paddle :result])

;; --- paddles -------------------------------------------------------------------

(law a-paddle-never-leaves-the-court
  (forall [y Int, k Key] (Paddle? (move-paddle y k))))

(law up-and-down-move-two-rows-to-the-wall
  (forall [y Paddle]
    (and (= (move-paddle y [:Up]) (max 0 (- y 2)))
         (= (move-paddle y [:Down]) (min (- H PH) (+ y 2)))
         (= (move-paddle y [:Idle]) y))))

(defn gap [p ball-y] (abs (- (+ p (quot PH 2)) ball-y)))

(defn closer-by-one? [p p2 ball-y]
  (and (Paddle? p2) (<= (abs (- p2 p)) 1)
       (<= (gap p2 ball-y) (gap p ball-y))
       (or (zero? (gap p ball-y)) (not (< 0 p (- H PH))) (< (gap p2 ball-y) (gap p ball-y)))))

(law the-cpu-paddle-closes-on-the-ball
  (forall [y Paddle, by Row] (closer-by-one? y (track y by) by)))

;; --- the ball --------------------------------------------------------------------

(defn pace-kept? [b b2]
  (let [[_ _ dx _] b
        [_ y2 dx2 dy2] b2]
    (and (= (abs dx) (abs dx2)) (Spin? dy2) (Row? y2))))

(law the-ball-stays-between-the-walls-at-its-pace
  (forall [b Ball, ly Paddle, ry Paddle] (pace-kept? b (advance b ly ry))))

(defn open-court? [b]
  (let [[x y _ _] b]
    (and (< (+ LEFT-X 3) x (- RIGHT-X 3)) (< 2 y (- H 3)))))

(law in-open-court-the-ball-travels-at-its-velocity
  (forall [b Ball, ly Paddle, ry Paddle]
    (=> (open-court? b)
        (= (advance b ly ry)
           (let [[x y dx dy] b] [(+ x dx) (+ y dy) dx dy])))))

(defn under? [paddle-y y] (and (<= paddle-y y) (< y (+ paddle-y PH))))

;; A paddle is a wall on its own rows: a ball in front of it is still in
;; front after a tick, unless it went by on a row the paddle does not cover.
;; However fast the ball, it cannot jump the paddle.
(defn held-by-left? [paddle-y b2]
  (let [[x2 y2] b2] (or (> x2 LEFT-X) (not (under? paddle-y y2)))))

(law the-left-paddle-stops-the-ball
  (forall [b Ball, ly Paddle, ry Paddle]
    (=> (> (first b) LEFT-X) (held-by-left? ly (advance b ly ry)))))

(defn held-by-right? [paddle-y b2]
  (let [[x2 y2] b2] (or (< x2 RIGHT-X) (not (under? paddle-y y2)))))

(law the-right-paddle-stops-the-ball
  (forall [b Ball, ly Paddle, ry Paddle]
    (=> (< (first b) RIGHT-X) (held-by-right? ry (advance b ly ry)))))

(law a-serve-goes-to-the-side-named
  (and (neg? (nth (serve [:Left]) 2)) (pos? (nth (serve [:Right]) 2))
       (Ball? (serve [:Left])) (Ball? (serve [:Right]))))

;; --- the game --------------------------------------------------------------------

(law a-game-starts-level (= [0 0] (scores (new-game))))

(defn one-point-at-most? [before after]
  (let [[a b] before [a2 b2] after]
    (and (<= a a2) (<= b b2) (<= (+ a2 b2) (inc (+ a b))))))

(law a-tick-scores-at-most-one-point
  (forall [g Live, k Key] (one-point-at-most? (scores g) (scores (step g k)))))

(law the-game-is-won-exactly-at-WIN
  (forall [g Live, k Key]
    (= (= :Won (phase-of (step g k)))
       (let [[ls rs] (scores (step g k))] (or (= ls WIN) (= rs WIN))))))

(law pausing-twice-changes-nothing
  (forall [g Playing] (= (step (step g [:Pause]) [:Pause]) g)))

(law a-paused-game-stands-still
  (forall [g Paused, k Key] (=> (not= :Pause (first k)) (= (step g k) g))))

(law a-serve-counts-down
  (forall [g Serving, k Key]
    (=> (not= :Pause (first k))
        (= (phase-of (step g k))
           (if (pos? (second (first g))) :Serving :Playing)))))

(law pause-after-a-win-starts-over
  (forall [g Won] (= (step g [:Pause]) (new-game))))
