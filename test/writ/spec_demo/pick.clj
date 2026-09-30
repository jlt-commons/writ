(ns writ.spec-demo.pick
  "One branch reads past the end of a literal vector, which throws: a law
  about the other branch is proved all the same.")

(defn pick [b]
  (if b "one" (str (nth [1 2] 5))))
