(ns writ.spec-demo.walk
  "Code that takes apart values of any shape: a structural matcher, and a
  count of a form's leaves.")

(defn capture
  "Match pattern p ([:Wild], [:Nil], [:Lit v], [:Bind s], [:Cons p q])
  against m: the bindings, or nil."
  [p m]
  (case (first p)
    :Wild {}
    :Nil  (if (and (sequential? m) (empty? m)) {} nil)
    :Lit  (if (= (nth p 1) m) {} nil)
    :Bind {(nth p 1) m}
    :Cons (let [[_ hd tl] p]
            (if (and (sequential? m) (seq m))
              (let [b (capture hd (first m))]
                (if (nil? b) nil (let [c (capture tl (rest m))] (if (nil? c) nil (merge b c)))))
              nil))))

(defn clause-of
  "The first of pats m matches: [:Hit k env], or [:Miss]."
  [pats m]
  (loop [ps (seq pats), k 0]
    (if ps
      (let [env (capture (first ps) m)]
        (if (some? env) [:Hit k env] (recur (next ps) (inc k))))
      [:Miss])))

(defn depth
  "How deeply form nests in its first elements."
  [form]
  (if (and (sequential? form) (seq form)) (inc (depth (first form))) 0))
