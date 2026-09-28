(ns writ.spec-demo.index
  "Loops whose index climbs to a bound: a search that resumes from a start,
  and a tally of the elements from an index on.")

(defn scan
  "The first index at or after start whose element is k: [:Take i], or
  [:None i] with i the index the search stopped at."
  [xs k start]
  (let [n (count xs)]
    (loop [i start]
      (if (< i n)
        (if (= k (nth xs i)) [:Take i] (recur (inc i)))
        [:None i]))))

(defn tally
  "How many elements of xs from index i on are k."
  [xs k i]
  (if (< i (count xs))
    (+ (if (= k (nth xs i)) 1 0) (tally xs k (inc i)))
    0))
