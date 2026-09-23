(ns writ.spec-demo.tree-typo
  "Broken: a clause names a constructor Tree does not have.")

(defn size [t]
  (case (first t)
    :Leaf 0
    :Nod (let [[_ l _ r] t] (+ 1 (size l) (size r)))
    0))

(defn to-list [t]
  (case (first t)
    :Leaf ()
    :Node (let [[_ l v r] t] (concat (to-list l) [v] (to-list r)))))

(defn insert [x t]
  (case (first t)
    :Leaf [:Node [:Leaf] x [:Leaf]]
    :Node (let [[_ l v r] t]
            (cond (< x v) [:Node (insert x l) v r]
                  (> x v) [:Node l v (insert x r)]
                  :else t))))
