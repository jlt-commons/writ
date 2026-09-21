(ns writ.quant
  "The quantity lattice: `:0` (erased), `:1` (affine, used once), `:w` (reusable).

  The order is 0 <= 1 <= w.  `meet` is the check kind's meet (min), `times`
  scales a usage by a binder's quantity, `add` adds usages (1+1 saturates to w),
  and `join` is the least upper bound used when branches meet."
  (:refer-clojure :exclude [add]))

(def q0 :0)
(def q1 :1)
(def qw :w)

(defn quant? [x] (contains? #{:0 :1 :w} x))

(defn leq [a b]
  (cond (not (quant? a)) (throw (ex-info "not a quantity" {:value a}))
        (not (quant? b)) (throw (ex-info "not a quantity" {:value b}))
        (= a :0) true
        (= b :w) true
        (= a :1) (= b :1)
        :else (= b :w)))

(defn meet [a b]
  (cond (= a :w) b
        (= b :w) a
        (= a :0) :0
        (= b :0) :0
        :else :1))

(defn times [a b]
  (cond (= a :0) :0
        (= a :1) b
        :else (if (= b :0) :0 :w)))

(defn add [a b]
  (if (or (= a :0) (= b :0))
    (if (= a :0) b a)
    :w))

(defn join [a b]
  (if (leq a b) b a))
