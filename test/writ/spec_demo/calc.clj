(ns writ.spec-demo.calc
  "Expressions compiled to instructions, the two sharing tags.")

(defn compile-expr [e]
  (case (first e)
    :num [[:push (second e)]]
    :add (let [[_ a b] e] (into (into (compile-expr a) (compile-expr b)) [[:add]]))
    :neg (let [[_ a] e] (conj (compile-expr a) [:neg]))))
