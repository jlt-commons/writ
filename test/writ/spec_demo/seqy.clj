(ns writ.spec-demo.seqy
  "Tests of seq? that are no map destructure, and an nth that may be of nil.")

(defn head-or [xs] (if (seq? xs) (first xs) xs))

(defn second-or [xs] (if (seq? xs) (second xs) xs))

(defn pick [xs] (if (nth xs 0) 1 2))
