(ns writ.spec-demo.turnstile
  "A coin-operated turnstile. A kick breaks it from anywhere; a repair puts
  it back, locked.")

(defn step [state event]
  (case (first event)
    :Kick [:Broken]
    :Coin (case (first state) :Locked [:Unlocked] :Unlocked state :Broken state)
    :Push (case (first state) :Unlocked [:Locked] :Locked state :Broken state)
    :Repair (case (first state) :Broken [:Locked] :Locked state :Unlocked state)))
