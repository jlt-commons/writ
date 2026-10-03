(ns writ.solve.lra
  "The general simplex of Dutertre and de Moura as a theory solver inside
  one DPLL(T) search, kept the way their paper and Yices and Z3 keep it:
  in place, and undone by its bounds alone.

  - A variable is a number.  Its value, its bounds and the literals they
    came from, its row when it is basic, and the basic variables whose
    rows hold it when it is not -- its column -- are arrays indexed by
    that number, changed in place.
  - Asserting a literal tightens a bound and notes the old one on a trail,
    with the place on the search's trail of the literal it came from.
    Backtracking puts back the bounds of the literals undone, and nothing
    else: a tableau is an identity whatever the bounds, and the values
    stay within the weaker bounds (Dutertre and de Moura, section 4.4).
  - A nonbasic variable always sits within its bounds; a new bound it
    breaks moves it there, and the basic variables of its column with it.
    The basic variables a move may have put out of bounds wait in a set,
    so a check with none there is done at once.
  - A check pivots the first such variable back, by Bland's rule, until
    none is left -- or one cannot move, and its row names the bounds that
    stop it: a Farkas certificate over their literals.

  Each inequality a.x <= c bounds a variable: x itself when a is a single
  unit coefficient, otherwise a slack s = a.x, one per distinct form up to
  sign, made when its first literal is asserted and kept for the rest of
  the search.  Everything is exact: rationals."
  (:require [writ.solve.simplex :as simplex]))

(defn- grow
  "Array a, at least n long."
  [^objects a n]
  (if (< (alength a) n)
    (let [b (object-array (max n (* 2 (alength a))))]
      (System/arraycopy a 0 b 0 (alength a))
      b)
    a))

(def ^:private slots
  "Where each part of a solver's state sits in its array."
  (zipmap [:max-pivots :ids :names :val :lo :lo-lit :hi :hi-lit :row :col
           :slacks :info :trail :open]
          (range)))

;; a part of the state, and a change to it: one read of the array at a
;; place fixed when this is compiled
(defmacro ^:private arr [st k] `(aget ~(with-meta st {:tag 'objects}) ~(get slots k)))
(defmacro ^:private put! [st k v] `(aset ~(with-meta st {:tag 'objects}) ~(get slots k) ~v))
(defn- part
  "The part k of the state, k known only when it runs: :lo or :hi."
  [^objects st k]
  (aget st (get slots k)))
(defmacro ^:private sw! [st k f & args]
  `(let [st# ~st] (aset ^objects st# ~(get slots k) (~f (aget ^objects st# ~(get slots k)) ~@args))))

(defn make
  "A theory solver for one search: at most max-pivots pivots a check.  Its
  state is an array: the variables by number (variable -> number, and
  back), their values, bounds and the literals the bounds came from, rows
  of the basic ones ({nonbasic coefficient}) and columns of the others
  (#{basic whose row holds it}); the slack of each form, what each literal
  bounds ([x side bound]), the trail of bounds replaced ([trail-pos x side
  old-bound old-lit]), and the basic variables that may be out of bounds."
  [max-pivots]
  (object-array [max-pivots {} [] (object-array 16)
                 (object-array 16) (object-array 16) (object-array 16) (object-array 16)
                 (object-array 16) (object-array 16)
                 {} {} [] #{}]))

(defn- value [st x] (aget ^objects (arr st :val) x))
(defn- row [st x] (aget ^objects (arr st :row) x))
(defn- col [st x] (or (aget ^objects (arr st :col) x) #{}))
(defn- set-val! [st x v] (aset ^objects (arr st :val) x v))
(defn- set-col! [st x c] (aset ^objects (arr st :col) x c))

(defn- var!
  "Variable v's number, a new nonbasic variable at 0 when it is new."
  [st v]
  (or (get (arr st :ids) v)
      (let [n (count (arr st :names))]
        (sw! st :val grow (inc n)) (sw! st :lo grow (inc n)) (sw! st :lo-lit grow (inc n))
        (sw! st :hi grow (inc n)) (sw! st :hi-lit grow (inc n))
        (sw! st :row grow (inc n)) (sw! st :col grow (inc n))
        (sw! st :ids assoc v n)
        (sw! st :names conj v)
        (set-val! st n 0)
        n)))

(defn- add-to-row
  "Row r (a map) plus k times row s, with the columns kept: basic variable
  b's entries that appear or vanish join or leave their columns."
  [st b r k s]
  (reduce-kv (fn [r y d]
               (let [old (get r y)
                     v (+ (or old 0) (* k d))]
                 (if (zero? v)
                   (do (when old (set-col! st y (disj (col st y) b))) (dissoc r y))
                   (do (when-not old (set-col! st y (conj (col st y) b))) (assoc r y v)))))
             r s))

(defn- slack!
  "The slack of form a (a map of variables to coefficients), a basic
  variable whose row is a over the nonbasic variables: a basic variable
  of a is put in by its own row."
  [st a]
  (or (get (arr st :slacks) a)
      (let [s (var! st [:slack a])
            r (reduce-kv (fn [r v k]
                           (let [x (var! st v)]
                             (if-let [rx (row st x)]
                               (add-to-row st s r k rx)
                               (add-to-row st s r k {x 1}))))
                         {} a)]
        (aset ^objects (arr st :row) s r)
        (set-val! st s (reduce-kv (fn [t y k] (+ t (* k (value st y)))) 0 r))
        (sw! st :slacks assoc a s)
        s)))

(defn- info!
  "What literal l, [:le a c], bounds: [x side bound]."
  [st [_ a c :as l]]
  (or (get (arr st :info) l)
      (let [i (if (and (= 1 (count a)) (#{1 -1} (val (first a))))
                (let [[v k] (first a) x (var! st v)]
                  (if (= 1 k) [x :hi c] [x :lo (- c)]))
                (let [n (into {} (map (fn [[x k]] [x (- k)])) a)]
                  (if-let [s (get (arr st :slacks) n)]
                    [s :lo (- c)]
                    [(slack! st a) :hi c])))]
        (sw! st :info assoc l i)
        i)))

(defn- update!
  "Move nonbasic x to v, and the basic variables of its column with it."
  [st x v]
  (let [d (- v (value st x))]
    (doseq [b (col st x)]
      (set-val! st b (+ (value st b) (* (get (row st b) x) d))))
    (sw! st :open into (col st x))
    (set-val! st x v)))

(defn assert!
  "Take literal l, asserted at place pos of the search's trail, as true.
  nil, or a conflict [[literal 1] [literal 1]] when its bound crosses the
  other bound of its variable."
  [st l pos]
  (let [[x side c] (info! st l)
        ^objects bs (part st side)
        ^objects ls (part st (if (= side :lo) :lo-lit :hi-lit))
        old (aget bs x)]
    (when (or (nil? old) (if (= side :hi) (< c old) (> c old)))
      (sw! st :trail conj [pos x side old (aget ls x)])
      (aset bs x c)
      (aset ls x l)
      (let [other (aget ^objects (part st (if (= side :lo) :hi :lo)) x)]
        (if (and other (if (= side :lo) (> c other) (< c other)))
          [[(aget ^objects (arr st :lo-lit) x) 1] [(aget ^objects (arr st :hi-lit) x) 1]]
          (do (if (row st x)
                (sw! st :open conj x)
                (when (if (= side :lo) (< (value st x) c) (> (value st x) c))
                  (update! st x c)))
              nil))))))

(defn backtrack!
  "Undo the bounds of the literals asserted at place pos of the search's
  trail or after."
  [st pos]
  (loop []
    (let [t (arr st :trail)]
      (when-let [[p x side old old-lit] (peek t)]
        (when (>= p pos)
          (aset ^objects (part st side) x old)
          (aset ^objects (part st (if (= side :lo) :lo-lit :hi-lit)) x old-lit)
          (sw! st :trail pop)
          (recur))))))

(defn- violation [st x]
  (let [v (value st x)
        lo (aget ^objects (arr st :lo) x)
        hi (aget ^objects (arr st :hi) x)]
    (cond (and lo (< v lo)) :lo
          (and hi (> v hi)) :hi)))

(defn- pivot!
  "Make basic xi nonbasic and nonbasic xj basic, xi set to v."
  [st xi xj v]
  (let [ri (row st xi)
        a (get ri xj)
        theta (/ (- v (value st xi)) a)
        others (disj (col st xj) xi)]
    ;; the values: xi to v, xj by theta, and the rows holding xj with it
    (set-val! st xi v)
    (set-val! st xj (+ (value st xj) theta))
    (doseq [b others]
      (set-val! st b (+ (value st b) (* (get (row st b) xj) theta))))
    ;; xj's row: xi's solved for xj
    (let [rj (reduce-kv (fn [m k c] (if (= k xj) m (assoc m k (- (/ c a))))) {xi (/ 1 a)} ri)]
      ;; xi's row leaves the columns of its entries; xj's joins them
      (doseq [k (keys ri) :when (not= k xj)]
        (set-col! st k (-> (col st k) (disj xi) (conj xj))))
      (set-col! st xi #{xj})
      (aset ^objects (arr st :row) xi nil)
      (set-col! st xj nil)
      (aset ^objects (arr st :row) xj rj)
      ;; each other row holding xj: xj put in from its new row
      (doseq [b others]
        (let [rb (row st b)
              c (get rb xj)]
          (aset ^objects (arr st :row) b (add-to-row st b (dissoc rb xj) c rj))))
      (sw! st :open into others)
      (sw! st :open conj xj))))

(defn- explain
  "The Farkas multipliers for basic x stuck below (side :lo) or above its
  bound: its own bound, and the bound of each variable of its row that
  stops it, weighted by the row's coefficient."
  [st x side]
  (let [lit (fn [y s] (aget ^objects (part st (if (= s :lo) :lo-lit :hi-lit)) y))
        other {:lo :hi :hi :lo}]
    (into [[(lit x side) 1]]
          (for [[y a] (sort-by key (row st x))]
            (if (pos? a)
              [(lit y (other side)) a]
              [(lit y side) (- a)])))))

(defn check!
  "Bring every basic variable within its bounds.  nil when they all are,
  or the Farkas certificate [[literal multiplier] ...] of a conflict.
  Throws ::simplex/budget after max-pivots pivots."
  [st]
  (loop [n 0]
    (when (> n (arr st :max-pivots))
      (throw (ex-info "simplex pivot budget exhausted" {::simplex/budget true})))
    ;; the violated basic variable first in order (Bland's rule); one
    ;; within its bounds stays so until a move makes it open again
    (let [open (into #{} (filter #(and (row st %) (violation st %))) (arr st :open))]
      (put! st :open open)
      (if (empty? open)
        nil
        (let [x (reduce min open)
              side (violation st x)
              target (aget ^objects (part st side) x)
              ;; below its lower bound it must rise, above its upper it must fall
              y (reduce-kv (fn [m y a]
                             (let [up (if (= side :lo) (pos? a) (neg? a))
                                   b (aget ^objects (part st (if up :hi :lo)) y)]
                               (if (and (or (nil? b) (if up (< (value st y) b) (> (value st y) b)))
                                        (or (nil? m) (< y m)))
                                 y m)))
                           nil (row st x))]
          (if y
            (do (pivot! st x y target) (recur (inc n)))
            (explain st x side)))))))

(defn model
  "The values of the variables, slacks left out."
  [st]
  (into {} (for [[v x] (arr st :ids) :when (not (and (vector? v) (= :slack (first v))))]
             [v (value st x)])))

(defn gomory
  "A Gomory cut for the satisfied tableau whose basic variable x has a
  fractional value and a row of nonbasic variables all at a bound, as the
  Chvatal-Gomory multipliers [[literal k] ...] that derive it, or nil;
  see writ.solve.simplex/gomory."
  [st]
  (let [frac #(- % (simplex/floor-value %))
        n (count (arr st :names))]
    (first
      (for [x (range n)
            :let [r (row st x)]
            :when (and r (not (integer? (value st x))))
            :let [terms (for [[y a] (sort-by key r)]
                          (let [lo (aget ^objects (arr st :lo) y) hi (aget ^objects (arr st :hi) y)]
                            (cond (and lo (= (value st y) lo)) [(aget ^objects (arr st :lo-lit) y) (frac a)]
                                  (and hi (= (value st y) hi)) [(aget ^objects (arr st :hi-lit) y) (frac (- a))])))]
            :when (every? some? terms)
            :let [terms (vec (remove (comp zero? second) terms))]
            :when (seq terms)]
        terms))))
