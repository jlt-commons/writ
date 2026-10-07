(ns writ.spec-demo.alarms
  "Alarms by ref, each with an optional repeat interval.")

(defn cancel
  "t without the alarm ref."
  [t ref]
  (filterv (fn [x] (case (first x) :Alarm (let [[_ r] x] (not= r ref)))) t))
