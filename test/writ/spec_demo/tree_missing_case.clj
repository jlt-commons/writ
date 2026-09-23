(ns writ.spec-demo.tree-missing-case
  "Broken: size forgets the empty tree.")

(defn size [t]
  (case (first t)
    :Node (let [[_ l _ r] t] (+ 1 (size l) (size r)))))

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
