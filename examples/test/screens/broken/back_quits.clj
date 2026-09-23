(ns screens.broken.back-quits
  "screens.core where Back on the pause screen quits to the title, when the
  table says it resumes the game. The game in progress is lost.")

(defn next-screen [screen event]
  (case (first screen)
    :Logo (case (first event) :Timeout [:Title] screen)
    :Title (case (first event) :Confirm [:Gameplay] :Configure [:Options] screen)
    :Options (case (first event) :Back [:Title] screen)
    :Gameplay (case (first event) :Pause [:Paused] :Finish [:Ending] screen)
    :Paused (case (first event) :Pause [:Gameplay] :Back [:Title] :Quit [:Title] screen)
    :Ending (case (first event) :Confirm [:Title] screen)))
