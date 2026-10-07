(ns writ.spec-demo.receive
  "Selective receive over tagged-data patterns: a pattern is matched
  against a message a level at a time.")

(defn capture
  "The bindings pattern p takes from message m, or nil when it does not
  match."
  [p m]
  (case (first p)
    :Wild {}
    :Nil  (if (and (sequential? m) (empty? m)) {} nil)
    :Lit  (if (= (nth p 1) m) {} nil)
    :Bind {(nth p 1) m}
    :Cons (let [[_ hd tl] p]
            (if (and (sequential? m) (seq m))
              (let [b (capture hd (first m))]
                (if (nil? b)
                  nil
                  (let [c (capture tl (rest m))]
                    (if (nil? c) nil (merge b c)))))
              nil))))

(defn clause-of
  "The first clause msg satisfies: [:Hit k env], or [:Miss]."
  [pats msg]
  (loop [ps (seq pats), k 0]
    (if ps
      (let [env (capture (first ps) msg)]
        (if (some? env)
          [:Hit k env]
          (recur (next ps) (inc k))))
      [:Miss])))

(defn scan
  "[:Take i k env]: message i is the first at or after start a clause
  takes.  [:None n]: none does, n the count scanned up to."
  [msgs pats start]
  (let [n (count msgs)]
    (loop [i start]
      (if (< i n)
        (let [r (clause-of pats (nth msgs i))]
          (case (first r)
            :Hit (let [[_ k env] r] [:Take i k env])
            :Miss (recur (inc i))))
        [:None i]))))
