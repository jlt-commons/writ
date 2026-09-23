(ns screens.main
  "raylib's screen manager (`jolt -M:screens`): a logo, a title, options,
  a game you can pause, and an ending. ENTER confirms, O opens the options,
  BACKSPACE goes back, P pauses, F finishes the game, Q quits to the title.

  The clock and the keys become events here; which screen follows is
  screens.core's, checked against the transition table in
  test/screens/core_spec.clj."
  (:require [net.b12n.raylib.all :as rl]
            [screens.core :as screens]))

(def W 800)
(def H 450)
(def logo-frames 120)

(def events
  [[:Timeout] [:Confirm] [:Configure] [:Back] [:Pause] [:Finish] [:Quit]])

(def key-of
  {:Confirm "ENTER" :Configure "O" :Back "BACKSPACE" :Pause "P" :Finish "F" :Quit "Q"})

(defn- event-now [screen frames-on-screen]
  (cond
    (and (= [:Logo] screen) (>= frames-on-screen logo-frames)) [:Timeout]
    (rl/key-pressed? rl/KEY-ENTER) [:Confirm]
    (rl/key-pressed? rl/KEY-O) [:Configure]
    (rl/key-pressed? rl/KEY-BACKSPACE) [:Back]
    (rl/key-pressed? rl/KEY-P) [:Pause]
    (rl/key-pressed? rl/KEY-F) [:Finish]
    (rl/key-pressed? rl/KEY-Q) [:Quit]
    :else nil))

(defn- help
  "The keys that do something on this screen, found by asking the pure
  core where each event would lead."
  [screen]
  (for [e events
        :let [k (key-of (first e))
              to (screens/next-screen screen e)]
        :when (and k (not= to screen))]
    (str k ": " (name (first to)))))

(def colors
  {:Logo rl/RAYWHITE :Title rl/DARKBLUE :Options rl/DARKPURPLE
   :Gameplay rl/DARKGREEN :Paused rl/DARKGRAY :Ending rl/MAROON})

(defn- draw [screen frames frame]
  (let [s (first screen)
        ink (if (= :Logo s) rl/DARKGRAY rl/RAYWHITE)]
    (rl/clear-background (colors s))
    (case s
      :Logo (rl/text! "writ" :x (- (/ W 2) 60) :y 180 :size 60 :color rl/DARKGRAY)
      :Gameplay (let [x (mod (* 4 frame) (* 2 (- W 40)))
                      x (if (> x (- W 40)) (- (* 2 (- W 40)) x) x)]
                  (rl/rect! :x x :y 300 :width 40 :height 40 :color rl/GOLD))
      nil)
    (rl/text! (name s) :x 40 :y 40 :size 40 :color ink)
    (doseq [[i line] (map-indexed vector (help screen))]
      (rl/text! line :x 40 :y (+ 110 (* 28 i)) :size 20 :color ink))
    (when (= :Logo s)
      (rl/text! (str (- logo-frames frames)) :x 40 :y 400 :size 20 :color ink))))

(defn -main [& _]
  (rl/window! :width W :height H :title "writ screens")
  (rl/set-target-fps 60)
  ;; WRIT_EXAMPLE_FRAMES=n closes the window after n frames, for a smoke run
  (let [limit (some-> (System/getenv "WRIT_EXAMPLE_FRAMES") parse-long)]
    (loop [frame 0, screen [:Logo], frames 0]
      (when-not (or (rl/window-should-close?) (and limit (>= frame limit)))
        (let [e (event-now screen frames)
              next (if e (screens/next-screen screen e) screen)]
          (rl/begin-drawing)
          (draw next (if (= next screen) frames 0) frame)
          (rl/end-drawing)
          (recur (inc frame) next (if (= next screen) (inc frames) 0))))))
  (rl/close-window))
