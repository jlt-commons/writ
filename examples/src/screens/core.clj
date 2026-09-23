(ns screens.core
  "Which screen a game shows, and what moves it to the next one: the
  screen manager from raylib's examples, as one pure fn.

  A screen is [:Logo], [:Title], [:Options], [:Gameplay], [:Paused] or
  [:Ending]; an event is [:Timeout], [:Confirm], [:Configure], [:Back],
  [:Pause], [:Finish] or [:Quit]. An event a screen has no use for leaves
  it where it is. screens.main turns keys and the clock into events.")

(defn next-screen [screen event]
  (case (first screen)
    :Logo (case (first event) :Timeout [:Title] screen)
    :Title (case (first event) :Confirm [:Gameplay] :Configure [:Options] screen)
    :Options (case (first event) :Back [:Title] screen)
    :Gameplay (case (first event) :Pause [:Paused] :Finish [:Ending] screen)
    :Paused (case (first event) :Pause [:Gameplay] :Back [:Gameplay] :Quit [:Title] screen)
    :Ending (case (first event) :Confirm [:Title] screen)))
