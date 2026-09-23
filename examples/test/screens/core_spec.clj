(ns screens.core-spec
  "The contract for screens.core: its transition table, and what the table
  itself must satisfy.

  The table is the whole meaning of `next-screen`. writ runs the fn on
  every screen and every event, 42 pairs, and each answer must be the
  table's, or the same screen where the table lists nothing. Then it checks
  the table against the rules a screen flow should keep: every screen
  leads back to the title, the logo shows only at startup, and there is no
  ending without play."
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
                 [:Options]  {[:Back] [:Title]}
                 [:Gameplay] {[:Pause] [:Paused], [:Finish] [:Ending]}
                 [:Paused]   {[:Pause] [:Gameplay], [:Back] [:Gameplay], [:Quit] [:Title]}
                 [:Ending]   {[:Confirm] [:Title]}}
   :final [[:Title]]
   :never [[[:Title] [:Logo]]]
   :before [[[:Gameplay] [:Ending]]
            [[:Title] [:Gameplay]]]})
