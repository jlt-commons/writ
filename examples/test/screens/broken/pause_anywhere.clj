(ns screens.broken.pause-anywhere
  "screens.core with pause made global: P pauses from any screen, so the
  title and the ending can be paused into a game that never started.")

(defn next-screen [screen event]
  (case (first event)
    :Pause (case (first screen) :Paused [:Gameplay] [:Paused])
    (case (first screen)
      :Logo (case (first event) :Timeout [:Title] screen)
      :Title (case (first event) :Confirm [:Gameplay] :Configure [:Options] screen)
      :Options (case (first event) :Back [:Title] screen)
      :Gameplay (case (first event) :Finish [:Ending] screen)
      :Paused (case (first event) :Back [:Gameplay] :Quit [:Title] screen)
      :Ending (case (first event) :Confirm [:Title] screen))))
