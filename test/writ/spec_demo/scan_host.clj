(ns writ.spec-demo.scan-host
  "Static host members and loops that are not a fn's last form, as scan
  sees them.")

(defn env [k] (System/getenv k))

(defn now [] (System/currentTimeMillis))

(defn touch-all [xs] (doseq [x xs] (inc x)) nil)

(defn loop-sum [xs] (loop [s 0 ys xs] (if (seq ys) (recur (+ s (first ys)) (rest ys)) s)))
