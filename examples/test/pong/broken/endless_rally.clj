(ns pong.broken.endless-rally
  "pong.core with a smarter CPU: it plays the ball forward to the row it will
  arrive on. Between two paddles that cover it, the ball never arrives.")

(def W 80)
(def H 45)
(def PH 8)
(def LEFT-X 2)
(def RIGHT-X 77)
(def WIN 5)
(def SERVE-TICKS 30)

(defn- clamp [lo hi v]
  (max lo (min hi v)))

(defn move-paddle
  "The player's paddle after one tick of `key`. Up and Down move it two
  rows; it never leaves the court."
  [y key]
  (case (first key)
    :Up (clamp 0 (- H PH) (- y 2))
    :Down (clamp 0 (- H PH) (+ y 2))
    :Idle (clamp 0 (- H PH) y)
    :Pause (clamp 0 (- H PH) y)))

(defn track
  "The CPU paddle after one tick: one row toward the ball's row."
  [y ball-y]
  (let [mid (+ y (quot PH 2))]
    (clamp 0 (- H PH) (cond (< mid ball-y) (inc y)
                            (> mid ball-y) (dec y)
                            :else y))))

(defn- covers? [paddle-y y]
  (and (<= paddle-y y) (< y (+ paddle-y PH))))

(defn- english
  "The spin a paddle puts on the ball: how far from the paddle's middle it
  was struck, as a row speed between -2 and 2."
  [paddle-y y]
  (clamp -2 2 (quot (- y (+ paddle-y (quot PH 2))) 2)))

(defn advance
  "The ball one tick on. It bounces off the top and bottom walls, and off a
  paddle that covers the row it crosses the paddle's column on."
  [ball ly ry]
  (let [[x y dx dy] ball
        y1 (+ y dy)
        [y2 dy2] (cond (< y1 0) [(- y1) (- dy)]
                       (>= y1 H) [(- (* 2 (dec H)) y1) (- dy)]
                       :else [y1 dy])
        x1 (+ x dx)]
    (cond
      (and (neg? dx) (> x LEFT-X) (<= x1 LEFT-X) (covers? ly y2))
      [(inc LEFT-X) y2 (- dx) (english ly y2)]

      (and (pos? dx) (< x RIGHT-X) (>= x1 RIGHT-X) (covers? ry y2))
      [(dec RIGHT-X) y2 (- dx) (english ry y2)]

      :else [x1 y2 dx dy2])))

(defn arrival-row
  "Where the ball will be when it reaches the right paddle's column."
  [ball ly ry]
  (loop [b ball]
    (if (< (first b) (dec RIGHT-X))
      (recur (advance b ly ry))
      (second b))))

(defn serve
  "A ball at the centre, heading for `side`."
  [side]
  (case (first side)
    :Left [(quot W 2) (quot H 2) -1 1]
    :Right [(quot W 2) (quot H 2) 1 -1]))

(defn new-game []
  [[:Serving SERVE-TICKS] (serve [:Right]) (quot (- H PH) 2) (quot (- H PH) 2) 0 0])

(defn play
  "One tick of play: the paddles move, the ball moves, and a ball past a
  goal line scores a point."
  [ball ly ry ls rs key]
  (let [ly2 (move-paddle ly key)
        ry2 (track ry (arrival-row ball ly ry))
        b (advance ball ly2 ry2)
        x (first b)]
    (cond
      (< x 0) (if (>= (inc rs) WIN)
                [[:Won [:Right]] b ly2 ry2 ls (inc rs)]
                [[:Serving SERVE-TICKS] (serve [:Left]) ly2 ry2 ls (inc rs)])
      (>= x W) (if (>= (inc ls) WIN)
                 [[:Won [:Left]] b ly2 ry2 (inc ls) rs]
                 [[:Serving SERVE-TICKS] (serve [:Right]) ly2 ry2 (inc ls) rs])
      :else [[:Playing] b ly2 ry2 ls rs])))

(defn step
  "The game one tick on, given the key held this tick. Pause stops and
  restarts play; after a win, Pause starts a new game."
  [game key]
  (let [[phase ball ly ry ls rs] game
        pause? (case (first key) :Pause true false)]
    (case (first phase)
      :Serving (let [[_ n] phase]
                 (cond pause? [[:Paused] ball ly ry ls rs]
                       (pos? n) [[:Serving (dec n)] ball (move-paddle ly key) ry ls rs]
                       :else [[:Playing] ball ly ry ls rs]))
      :Playing (if pause?
                 [[:Paused] ball ly ry ls rs]
                 (play ball ly ry ls rs key))
      :Paused (if pause? [[:Playing] ball ly ry ls rs] game)
      :Won (if pause? (new-game) game))))
