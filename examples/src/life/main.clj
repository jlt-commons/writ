(ns life.main
  "The Game of Life in a raylib window (`jolt -M:life`). SPACE sows a new
  random soup, F switches between life.core and life.fast; both meet the
  same spec, so the picture must not change when you switch.

  Randomness, time and drawing are effects and live here. The rules are in
  life.core and life.fast, checked by test/life/core_spec.clj."
  (:require [life.core :as core]
            [life.fast :as fast]
            [net.b12n.raylib.all :as rl]))

(def cols 120)
(def rows 68)
(def cell 8)
(def frames-per-generation 4)
(def margin 10)

(defn- soup []
  (set (for [x (range cols) y (range rows) :when (< (rand) 0.3)] [x y])))

(defn- on-board
  "The plane is unbounded, the window is not: cells that wander more than
  `margin` beyond the edge are let go."
  [world]
  (set (filter (fn [[x y]] (and (< (- margin) x (+ cols margin))
                                (< (- margin) y (+ rows margin))))
               world)))

(defn- draw [world impl generation]
  (rl/clear-background (rl/rgba 8 10 14 255))
  (doseq [[x y] world :when (and (< -1 x cols) (< -1 y rows))]
    (rl/rect! :x (* x cell) :y (* y cell) :width (dec cell) :height (dec cell)
              :color rl/LIME))
  (rl/rect! :x 0 :y 0 :width (* cols cell) :height 28 :color (rl/rgba 8 10 14 220))
  (rl/text! (str "generation " generation "   " (count world) " cells   "
                 (name impl) "   SPACE new soup, F switch")
            :x 8 :y 6 :size 18 :color rl/RAYWHITE))

(defn -main [& _]
  (rl/window! :width (* cols cell) :height (* rows cell) :title "writ life")
  (rl/set-target-fps 60)
  ;; WRIT_EXAMPLE_FRAMES=n closes the window after n frames, for a smoke run
  (let [limit (some-> (System/getenv "WRIT_EXAMPLE_FRAMES") parse-long)]
    (loop [frame 0, world (soup), impl :core, generation 0]
      (when-not (or (rl/window-should-close?) (and limit (>= frame limit)))
        (let [impl (if (rl/key-pressed? rl/KEY-F) ({:core :fast :fast :core} impl) impl)
              step (if (= :fast impl) fast/step core/step)
              [world generation] (cond
                                   (rl/key-pressed? rl/KEY-SPACE) [(soup) 0]
                                   (zero? (mod frame frames-per-generation))
                                   [(on-board (step world)) (inc generation)]
                                   :else [world generation])]
          (rl/begin-drawing)
          (draw world impl generation)
          (rl/end-drawing)
          (recur (inc frame) world impl generation)))))
  (rl/close-window))
