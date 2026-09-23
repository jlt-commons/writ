(ns writ.spec-demo.turnstile-no-repair
  "A turnstile that stays broken, matching a spec whose table forgot the
  repair.")

(defn step [state event]
  (case (first state)
    :Broken state
    :Locked (case (first event) :Coin [:Unlocked] :Kick [:Broken] state)
    :Unlocked (case (first event) :Push [:Locked] :Kick [:Broken] state)))
