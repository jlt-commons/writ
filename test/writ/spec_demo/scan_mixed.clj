(ns writ.spec-demo.scan-mixed
  "A namespace that mixes pure fns with IO, the way a binding library
  does. writ.spec/scan says which of its fns a spec could cover.")

(defn classify [n]
  (cond (pos? n) :data
        (= n -1) :error
        :else :idle))

(defn- shout [s]
  (.toUpperCase s))

(defn log! [x]
  (println x)
  x)

(defn loud-classify [n]
  (shout (name (classify n))))

(defrecord Conn [fd])

(defn total [xs]
  (if (seq xs) (+ (first xs) (total (rest xs))) 0))
