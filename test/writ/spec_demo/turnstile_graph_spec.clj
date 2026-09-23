(ns writ.spec-demo.turnstile-graph-spec
  "A table with a trap in it, and path constraints it breaks."
  (:require [writ.spec :refer [spec data ann machine]]))

(spec writ.spec-demo.turnstile-no-repair)

(data State Locked Unlocked Broken)
(data Event Coin Push Kick Repair)

(ann step [State Event -> State])

(machine turnstile
  {:step step
   :start [:Locked]
   :transitions {[:Locked] {[:Coin] [:Unlocked], [:Kick] [:Broken]}
                 [:Unlocked] {[:Push] [:Locked], [:Kick] [:Broken]}}
   :final [[:Locked]]
   :never [[[:Unlocked] [:Broken]]]
   :before [[[:Unlocked] [:Broken]]]})
