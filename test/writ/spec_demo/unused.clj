(ns writ.spec-demo.unused
  "A binding whose value is never used, which still runs: nth past the
  end of a short vector throws.")

(defn pick [v]
  (let [x (nth v 3)]
    0))
