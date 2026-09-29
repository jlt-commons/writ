(ns writ.spec-demo.spin
  "A pair of states that hand a count back and forth, and never finish.")

(defn flip [s]
  (let [[phase n] s]
    (case phase
      :A [:B n]
      :B [:A n]
      :Done s)))
