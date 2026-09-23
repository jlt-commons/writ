(ns writ.spec-demo.turnstile-spec
  (:require [writ.spec :refer [spec data ann law machine]]))

(spec writ.spec-demo.turnstile)

(data State Locked Unlocked Broken)
(data Event Coin Push Kick Repair)

(ann step [State Event -> State])

(machine turnstile
  {:step step
   :start [:Locked]
   :transitions {[:Locked] {[:Coin] [:Unlocked], [:Kick] [:Broken]}
                 [:Unlocked] {[:Push] [:Locked], [:Kick] [:Broken]}
                 [:Broken] {[:Repair] [:Locked]}}
   :final [[:Locked]]
   :before [[[:Locked] [:Unlocked]]]})
