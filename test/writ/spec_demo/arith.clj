(ns writ.spec-demo.arith
  "Arithmetic expressions: their value under an environment, a bottom-up
  simplifier, their node count and their variables.

  Plain Clojure.  A tagged data value is taken apart with `case` on its
  tag; the simplified children of a node are numeric or not, and that
  test goes through `case` too, since a tagged value is read only that
  way.")

(defn- num-value
  "The Int in a [:num n], or nil when e is any other expression."
  [e]
  (case (first e)
    :num (let [[_ n] e] n)
    :var nil
    :add nil
    :mul nil
    :neg nil))

(defn- neg-inner
  "The x in a [:neg x], or nil when e is any other expression."
  [e]
  (case (first e)
    :num nil
    :var nil
    :add nil
    :mul nil
    :neg (let [[_ x] e] x)))

(defn- simplify-add
  "The first add rule that matches the node [:add a b] of simplified
  parts, once."
  [a b]
  (let [av (num-value a)
        bv (num-value b)]
    (cond
      (and av bv) [:num (+ av bv)]
      (= 0 av) b
      (= 0 bv) a
      :else [:add a b])))

(defn- simplify-mul
  "The first mul rule that matches the node [:mul a b] of simplified
  parts, once."
  [a b]
  (let [av (num-value a)
        bv (num-value b)]
    (cond
      (and av bv) [:num (* av bv)]
      (= 1 av) b
      (= 1 bv) a
      (or (= 0 av) (= 0 bv)) [:num 0]
      :else [:mul a b])))

(defn- simplify-neg
  "The first neg rule that matches the node [:neg a] of a simplified
  part, once."
  [a]
  (let [av (num-value a)
        inner (neg-inner a)]
    (cond
      av (let [[_ n] a] [:num (- n)])
      inner inner
      :else [:neg a])))

(defn evaluate
  "The Int value of e under env; a variable env does not have is 0."
  [e env]
  (case (first e)
    :num (let [[_ n] e] n)
    :var (let [[_ k] e] (get env k 0))
    :add (let [[_ a b] e] (+ (evaluate a env) (evaluate b env)))
    :mul (let [[_ a b] e] (* (evaluate a env) (evaluate b env)))
    :neg (let [[_ a] e] (- (evaluate a env)))))

(defn simplify
  "Simplify e bottom-up: simplify its parts, then apply the first
  matching rule once."
  [e]
  (case (first e)
    :num e
    :var e
    :add (let [[_ a b] e] (simplify-add (simplify a) (simplify b)))
    :mul (let [[_ a b] e] (simplify-mul (simplify a) (simplify b)))
    :neg (let [[_ a] e] (simplify-neg (simplify a)))))

(defn size
  "The number of nodes in e."
  [e]
  (case (first e)
    :num 1
    :var 1
    :add (let [[_ a b] e] (+ 1 (size a) (size b)))
    :mul (let [[_ a b] e] (+ 1 (size a) (size b)))
    :neg (let [[_ a] e] (+ 1 (size a)))))

(defn variables
  "The distinct keywords e mentions, sorted, as a vector."
  [e]
  (case (first e)
    :num []
    :var (let [[_ k] e] [k])
    :add (let [[_ a b] e] (vec (sort (distinct (concat (variables a) (variables b))))))
    :mul (let [[_ a b] e] (vec (sort (distinct (concat (variables a) (variables b))))))
    :neg (let [[_ a] e] (variables a))))
