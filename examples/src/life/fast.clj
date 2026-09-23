(ns life.fast
  "life.core rewritten for speed: one pass counts, for every cell next to
  a live one, how many live cells touch it. Nothing about the rule is
  restated here; it has to agree with life.core's spec, and the spec is
  checked against it with `:target`.")

(defn neighbours [cell]
  (let [[x y] cell]
    #{[(dec x) (dec y)] [x (dec y)] [(inc x) (dec y)]
      [(dec x) y] [(inc x) y]
      [(dec x) (inc y)] [x (inc y)] [(inc x) (inc y)]}))

(defn step [world]
  (set (keep (fn [[cell n]]
               (when (or (= n 3) (and (= n 2) (contains? world cell)))
                 cell))
             (frequencies (mapcat neighbours world)))))
