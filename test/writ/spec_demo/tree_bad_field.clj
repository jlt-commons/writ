(ns writ.spec-demo.tree-bad-field
  "Broken: insert puts the value where the left subtree goes.")

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
    :Leaf [:Node x [:Leaf] [:Leaf]]
    :Node (let [[_ l v r] t]
            (cond (< x v) [:Node (insert x l) v r]
                  (> x v) [:Node l v (insert x r)]
                  :else t))))
