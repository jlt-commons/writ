(ns writ.spec-demo.verdict-core
  "The reasons a stop is orderly: the helper a pure core in another
  namespace relies on.")

(defn orderly? [r] (or (= :normal r) (= :shutdown r)))
