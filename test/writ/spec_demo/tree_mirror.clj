(ns writ.spec-demo.tree-mirror
  "Broken: insert sends smaller values right, so in-order is not ascending.")

(defn size [t]
  (case (first t)
    :Leaf 0
    :Node (let [[_ l _ r] t] (+ 1 (size l) (size r)))))

(defn to-list [t]
  (case (first t)
    :Leaf ()
    :Node (let [[_ l v r] t] (concat (to-list l) [v] (to-list r)))))

(defn insert [x t]
  (case (first t)
    :Leaf [:Node [:Leaf] x [:Leaf]]
    :Node (let [[_ l v r] t]
            (cond (< x v) [:Node l v (insert x r)]
                  (> x v) [:Node (insert x l) v r]
                  :else t))))
