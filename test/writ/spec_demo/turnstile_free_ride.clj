(ns writ.spec-demo.turnstile-free-ride
  "Broken: a coin in a broken turnstile opens it.")

(defn step [state event]
  (case (first event)
    :Kick [:Broken]
    :Coin (case (first state) :Locked [:Unlocked] :Unlocked state :Broken [:Unlocked])
    :Push (case (first state) :Unlocked [:Locked] :Locked state :Broken state)
    :Repair (case (first state) :Broken [:Locked] :Locked state :Unlocked state)))
