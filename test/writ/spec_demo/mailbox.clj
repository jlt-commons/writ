(ns writ.spec-demo.mailbox
  "Erlang's selective receive over a mailbox vector: the first message, at
  or after start, that some clause takes.")

(defn- capture
  "A pattern is :_, taking anything, or a value taking itself: {} when it
  takes msg, nil when not."
  [pat msg]
  (when (or (= :_ pat) (= pat msg)) {}))

(defn clause-of
  "The first clause msg satisfies: [:Hit k env], or [:Miss]."
  [pats ok? msg]
  (loop [ps (seq pats), k 0]
    (if ps
      (let [env (capture (first ps) msg)]
        (if (and (some? env) (ok? k env))
          [:Hit k env]
          (recur (next ps) (inc k))))
      [:Miss])))

(defn scan
  "[:Take i k env]: message i is the first at or after start a clause takes.
  [:None n]: none does, n the count scanned up to."
  [msgs pats ok? start]
  (let [n (count msgs)]
    (loop [i start]
      (if (< i n)
        (let [r (clause-of pats ok? (nth msgs i))]
          (case (first r)
            :Hit (let [[_ k env] r] [:Take i k env])
            :Miss (recur (inc i))))
        [:None i]))))

