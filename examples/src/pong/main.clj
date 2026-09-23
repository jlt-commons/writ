(ns pong.main
  "Pong in a raylib window (`jolt -M:raylib:pong`). W/S or the arrow keys move the
  left paddle, P or SPACE pauses, and after a win it starts a new game.

  Everything here is effect: reading keys, drawing, the frame loop. The
  rules live in pong.core, which writ checks against test/pong/core_spec.clj."
  (:require [net.b12n.raylib.all :as rl]
            [pong.core :as pong]))

(def cell 10)
(def frames-per-tick 2)

(defn- key-held []
  (cond (or (rl/key-pressed? rl/KEY-P) (rl/key-pressed? rl/KEY-SPACE)) [:Pause]
        (or (rl/key-down? rl/KEY-W) (rl/key-down? rl/KEY-UP)) [:Up]
        (or (rl/key-down? rl/KEY-S) (rl/key-down? rl/KEY-DOWN)) [:Down]
        :else [:Idle]))

(defn- draw [[phase [bx by] ly ry ls rs]]
  (rl/clear-background (rl/rgba 12 12 20 255))
  (doseq [y (range 0 pong/H 3)]
    (rl/rect! :x (- (* cell (quot pong/W 2)) 1) :y (* y cell) :width 2 :height cell
              :color rl/GRAY))
  (rl/rect! :x (* cell pong/LEFT-X) :y (* cell ly) :width cell :height (* cell pong/PH)
            :color rl/RAYWHITE)
  (rl/rect! :x (* cell pong/RIGHT-X) :y (* cell ry) :width cell :height (* cell pong/PH)
            :color rl/RAYWHITE)
  (when (not= :Won (first phase))
    (rl/rect! :x (* cell bx) :y (* cell by) :width cell :height cell :color rl/GOLD))
  (rl/text! (str ls) :x (- (* cell (quot pong/W 2)) 80) :y 20 :size 50 :color rl/RAYWHITE)
  (rl/text! (str rs) :x (+ (* cell (quot pong/W 2)) 50) :y 20 :size 50 :color rl/RAYWHITE)
  (case (first phase)
    :Paused (rl/text! "PAUSED" :x 330 :y 200 :size 40 :color rl/GOLD)
    :Won (rl/text! (str (if (= :Left (first (second phase))) "YOU WIN" "CPU WINS")
                        "  -  P to play again")
                   :x 180 :y 200 :size 36 :color rl/GOLD)
    nil))

(defn -main [& _]
  (rl/window! :width (* cell pong/W) :height (* cell pong/H) :title "writ pong")
  (rl/set-target-fps 60)
  ;; WRIT_EXAMPLE_FRAMES=n closes the window after n frames, for a smoke run
  (let [limit (some-> (System/getenv "WRIT_EXAMPLE_FRAMES") parse-long)]
    (loop [frame 0, game (pong/new-game), key [:Idle]]
      (when-not (or (rl/window-should-close?) (and limit (>= frame limit)))
        ;; a pause press is kept until the tick that reads it
        (let [k (let [now (key-held)] (if (= [:Pause] key) key now))
              tick? (zero? (mod frame frames-per-tick))
              game (if tick? (pong/step game k) game)]
          (rl/begin-drawing)
          (draw game)
          (rl/end-drawing)
          (recur (inc frame) game (if tick? [:Idle] k))))))
  (rl/close-window))
