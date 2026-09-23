(ns screens.draft-spec
  "An early draft of the table, kept to show that writ checks the table as
  well as the code. It sends Quit on the pause screen to the logo, and it
  forgot that the options screen needs a way back. The code does neither,
  so it fails the table too; the point here is what writ says about the
  table itself."
  (:require [writ.spec :refer [spec data ann machine]]))

(spec screens.core)

(data Screen Logo Title Options Gameplay Paused Ending)
(data Event Timeout Confirm Configure Back Pause Finish Quit)

(ann next-screen [Screen Event -> Screen])

(machine screens
  {:step next-screen
   :start [:Logo]
   :transitions {[:Logo]     {[:Timeout] [:Title]}
                 [:Title]    {[:Confirm] [:Gameplay], [:Configure] [:Options]}
                 [:Gameplay] {[:Pause] [:Paused], [:Finish] [:Ending]}
                 [:Paused]   {[:Pause] [:Gameplay], [:Back] [:Gameplay], [:Quit] [:Logo]}
                 [:Ending]   {[:Confirm] [:Title]}}
   :final [[:Title]]
   :never [[[:Title] [:Logo]]]
   :before [[[:Gameplay] [:Ending]]
            [[:Title] [:Gameplay]]]})
