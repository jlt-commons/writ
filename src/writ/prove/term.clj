(ns writ.prove.term
  "The prover's terms, and their meaning as Clojure values.

  The value model follows Typed Clojure: nil and an empty collection are
  different values, and `seq` is the only way between them.  Every
  sequential value -- list, vector, cons, lazy seq -- is one term,
  [:sq E], since the ops the prover models treat them alike; the ops that
  tell them apart (conj, peek, vector?, ...) are outside the model.

    [:nil]                 nil
    [:lit v]               a number, string, keyword, char or boolean
    [:sq E]                a sequential value with elements E
    [:enil]                no elements
    [:econs h E]           h, then E
    [:eapp E1 E2]          E1's elements, then E2's
    [:elems v]             the elements of value v (nil has none)
    [:call f a ...]        a clojure.core fn applied
    [:app f a ...]         a fn of the target or the spec applied
    [:fn [p ...] body]     a fn value
    [:cfn f]               the clojure.core fn f, as a value
    [:dfn f]               the target's or the spec's fn f, as a value
    [:ap f a ...]          a fn value applied
    [:if c a b]            Clojure's if: b when c is nil or false
    [:lin c [[t k] ...]]   the integer c + k*t + ...
    [:le d]                0 <= d, for an integer d
    [:ieq d]               d = 0, for an integer d
    [:bottom]              a term that throws
    sym                    a variable

  `evaluate` gives a term its meaning by running it: the rewrite rules are
  checked against it, so each one agrees with the runtime.")

(def tnil [:nil])
(def enil [:enil])

(defn lit [v] (if (nil? v) tnil [:lit v]))

(defn head [t] (when (vector? t) (first t)))

(defn lit? [t] (= :lit (head t)))

(defn int-lit? [t] (and (lit? t) (integer? (second t))))

(defn elems-of [xs] (reduce (fn [e x] [:econs x e]) enil (reverse xs)))

(defn seq-term [xs] [:sq (elems-of xs)])

(defn value->term
  "The term for a Clojure value: nil, a literal, or a sequential of them."
  [v]
  (cond
    (nil? v) tnil
    (sequential? v) (seq-term (map value->term v))
    :else [:lit v]))

(defn sort-printed
  "xs in the order they print, or (kf x) prints: terms have no order of
  their own, and this one is the same on every run.  Each is printed once;
  sort-by with pr-str prints both sides of every comparison."
  ([xs] (sort-printed identity xs))
  ([kf xs] (map peek (sort-by first (map (fn [x] [(pr-str (kf x)) x]) xs)))))

(defn var? [t] (symbol? t))

(defn vars
  "The free variables of a term."
  [t]
  (cond
    (symbol? t) #{t}
    (not (vector? t)) #{}
    (= :fn (head t)) (let [[_ ps body] t] (apply disj (vars body) ps))
    (= :lin (head t)) (into #{} (mapcat (fn [[a _]] (vars a))) (nth t 2))
    (contains? #{:lit :cfn :dfn} (head t)) #{}
    ;; a call's head is the name of a fn, not a variable
    (contains? #{:call :app} (head t)) (into #{} (mapcat vars) (drop 2 t))
    :else (into #{} (mapcat vars) (rest t))))

(defn subst
  "Replace variables by terms: m is sym -> term.  A fn's own parameters
  hide the outer binding, and are renamed when a substituted term
  mentions them, so its variables are not captured.  A quoted symbol is
  data, not a variable."
  [t m]
  (cond
    (symbol? t) (get m t t)
    (not (vector? t)) t
    (contains? #{:lit :nil :enil :bottom :cfn :dfn} (head t)) t
    (= :fn (head t)) (let [[_ ps body] t
                           m* (apply dissoc m ps)
                           free (into #{} (comp (filter #(contains? (vars body) (key %)))
                                                (mapcat (comp vars val)))
                                      m*)
                           ren (into {} (keep (fn [p] (when (contains? free p)
                                                         [p (gensym (str (name p) "%"))])))
                                     ps)]
                       [:fn (mapv #(get ren % %) ps) (subst body (merge m* ren))])
    (= :lin (head t)) (let [[_ c pairs] t]
                        [:lin c (mapv (fn [[a k]] [(subst a m) k]) pairs)])
    (contains? #{:call :app} (head t)) (into [(first t) (second t)] (map #(subst % m)) (drop 2 t))
    :else (into [(first t)] (map #(subst % m)) (rest t))))

(defn subterms [t]
  (tree-seq (fn [x] (and (vector? x) (not (lit? x)) (not (contains? #{:cfn :dfn} (head x)))))
            (fn [x] (case (head x)
                      :lin (map first (nth x 2))
                      (:call :app) (drop 2 x)
                      (rest x)))
            t))

;; --- meaning ---------------------------------------------------------------

(declare evaluate)

(defn- eval-elems [e env]
  (case (head e)
    :enil ()
    :econs (cons (evaluate (nth e 1) env) (eval-elems (nth e 2) env))
    :eapp (concat (eval-elems (nth e 1) env) (eval-elems (nth e 2) env))
    :elems (seq (evaluate (nth e 1) env))
    (if (symbol? e) (seq (get env e)) (throw (ex-info "not elements" {:term e})))))

(defn evaluate
  "Run a term.  env is sym -> value; resolve turns an :app name into a fn."
  ([t] (evaluate t {}))
  ([t env] (evaluate t env resolve))
  ([t env res]
   (let [ev #(evaluate % env res)]
     (cond
       (symbol? t) (if (contains? env t) (get env t)
                       (throw (ex-info (str "unbound " t) {})))
       (not (vector? t)) t
       :else
       (case (head t)
         :nil nil
         :lit (second t)
         :sq (apply list (eval-elems (second t) env))
         (:enil :econs :eapp :elems) (apply list (eval-elems t env))
         :call (apply @(resolve (symbol "clojure.core" (name (second t))))
                      (map ev (drop 2 t)))
         :app (apply @(res (second t)) (map ev (drop 2 t)))
         :fn (let [[_ ps body] t]
               (fn [& args] (evaluate body (merge env (zipmap ps args)) res)))
         :cfn @(resolve (symbol "clojure.core" (name (second t))))
         :dfn @(res (second t))
         :ap (apply (ev (second t)) (map ev (drop 2 t)))
         :if (if (ev (nth t 1)) (ev (nth t 2)) (ev (nth t 3)))
         :lin (reduce + (second t) (map (fn [[a k]] (* k (ev a))) (nth t 2)))
         :le (<= 0 (ev (second t)))
         :ieq (= 0 (ev (second t)))
         :bottom (throw (ex-info "bottom" {}))
         (throw (ex-info (str "unknown term " (pr-str t)) {})))))))

;; --- showing terms ---------------------------------------------------------

(declare show)

(defn- show-lin [c pairs]
  (let [pos (concat (for [[a k] pairs :when (pos? k)] (if (= 1 k) (show a) (list '* k (show a))))
                    (when (pos? c) [c]))
        neg (concat (for [[a k] pairs :when (neg? k)] (if (= -1 k) (show a) (list '* (- k) (show a))))
                    (when (neg? c) [(- c)]))
        side (fn [xs] (cond (empty? xs) 0 (= 1 (count xs)) (first xs) :else (apply list '+ xs)))]
    [(side pos) (side neg)]))

(defn show
  "A term as the Clojure form it stands for, for reports."
  [t]
  (cond
    (symbol? t) t
    (not (vector? t)) t
    :else
    (case (head t)
      :nil nil
      :lit (second t)
      :sq (let [[xs tail] (loop [e (second t), xs []]
                            (if (= :econs (head e)) (recur (nth e 2) (conj xs (show (nth e 1)))) [xs e]))
                tail* (case (head tail)
                        :enil nil
                        :elems (show (second tail))
                        :eapp (list 'concat (show [:sq (nth tail 1)]) (show [:sq (nth tail 2)]))
                        tail)]
            (cond (nil? tail*) (apply list 'list xs)
                  (empty? xs) tail*
                  :else (list 'concat (apply list 'list xs) tail*)))
      :call (apply list (second t) (map show (drop 2 t)))
      :app (apply list (symbol (name (second t))) (map show (drop 2 t)))
      :fn (list 'fn (nth t 1) (show (nth t 2)))
      :cfn (second t)
      :dfn (symbol (name (second t)))
      :ap (apply list (show (second t)) (map show (drop 2 t)))
      :if (list 'if (show (nth t 1)) (show (nth t 2)) (show (nth t 3)))
      :lin (let [[p n] (show-lin (second t) (nth t 2))]
             (if (= 0 n) p (list '- p n)))
      :le (let [[_ c pairs] (let [d (second t)] (if (= :lin (head d)) d [:lin 0 [[d 1]]]))
                [p n] (show-lin c pairs)]
            (list '<= n p))
      :ieq (let [[_ c pairs] (let [d (second t)] (if (= :lin (head d)) d [:lin 0 [[d 1]]]))
                 [p n] (show-lin c pairs)]
             (list '= p n))
      t)))
