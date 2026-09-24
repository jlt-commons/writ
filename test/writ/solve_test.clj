(ns writ.solve-test
  "The solver: its answers on known formulas, its agreement with brute
  force on random ones, and the checker's refusal of a tampered proof."
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.walk :as walk]
            [clojure.test.check :as tc]
            [clojure.test.check.generators :as gen]
            [clojure.test.check.properties :as prop]
            [writ.solve :as s]))

(defn- unsat? [f & [decls]]
  (let [r (s/check f (or decls {}) {})]
    (and (= :unsat (:result r)) (s/verify f (or decls {}) (:certificate r)))))

(defn- sat-model [f & [decls]]
  (let [r (s/check f (or decls {}) {})]
    (when (= :sat (:result r))
      (when (s/eval-formula f (:model r)) (:model r)))))

(defn- valid? [f & [decls]]
  (let [r (s/valid? f (or decls {}) {})]
    (and (= :valid (:result r)) (s/verify f (or decls {}) (:certificate r)))))

(defn- invalid-model [f & [decls]]
  (let [r (s/valid? f (or decls {}) {})]
    (when (= :invalid (:result r))
      (when-not (s/eval-formula f (:model r)) (:model r)))))

;; --- simple cases ------------------------------------------------------------

(deftest constants
  (is (sat-model true))
  (is (unsat? false))
  (is (unsat? [:< 1 0]))
  (is (sat-model [:<= 0 0])))

(deftest linear-sat-and-unsat
  (is (sat-model [:and [:< 'x 'y] [:< 'y 3] [:> 'x 0]]))
  (is (unsat? [:and [:< 'x 'y] [:< 'y 'z] [:< 'z 'x]]))
  (is (unsat? [:and [:<= [:+ 'x 'y] 3] [:>= 'x 2] [:>= 'y 2]]))
  (is (= {'x 1 'y 2} (select-keys (sat-model [:and [:= 'x 1] [:= [:+ 'x 'y] 3]]) '[x y])))
  (is (unsat? [:and [:= 'x 1] [:distinct 'x 'y] [:= 'y 1]]))
  (is (sat-model [:distinct 'x 'y 'z]))
  (is (unsat? [:and [:distinct 'x 'y 'z] [:<= 0 'x 1] [:<= 0 'y 1] [:<= 0 'z 1]]
              {})
      "three distinct values in {0,1} is impossible"))

(deftest boolean-structure
  (is (unsat? [:and 'p [:not 'p]] {'p :bool}))
  (is (valid? [:or 'p [:not 'p]] {'p :bool}))
  (is (valid? [:iff [:=> 'p 'q] [:or [:not 'p] 'q]] {'p :bool 'q :bool}))
  (is (invalid-model [:=> 'p 'q] {'p :bool 'q :bool}))
  (is (valid? [:=> [:and [:< 'x 5] [:or [:= 'x 1] [:= 'x 7]]] [:= 'x 1]])))

(deftest nonlinear-products-are-rejected
  (is (thrown? clojure.lang.ExceptionInfo (s/check [:= [:* 'x 'y] 1] {} {})))
  (is (= :writ.solve/unsupported
         (try (s/check [:= [:* 'x 'y] 1] {} {}) nil
              (catch clojure.lang.ExceptionInfo e
                (some #{:writ.solve/unsupported} (keys (ex-data e))))))))

(deftest products-with-a-literal-either-side
  (is (valid? [:= [:* 2 'x] [:* 'x 2]]))
  (is (valid? [:= [:* 3 [:+ 'x 1]] [:+ [:* 3 'x] 3]])))

;; --- mod and quot follow clojure.core ----------------------------------------

(deftest mod-bounds
  (is (unsat? [:and [:<= 0 'x] [:< 'x 10] [:= 'y [:mod [:+ 'x 3] 10]]
               [:not [:and [:<= 0 'y] [:< 'y 10]]]]))
  (is (valid? [:and [:<= 0 [:mod 'x 7]] [:< [:mod 'x 7] 7]]))
  (is (valid? [:and [:< -7 [:mod 'x -7]] [:<= [:mod 'x -7] 0]])))

(deftest mod-and-quot-agree-with-clojure-core
  (doseq [a (range -9 10) k [-4 -3 -1 1 2 5]]
    (is (valid? [:= [:mod a k] (mod a k)]) (str "(mod " a " " k ")"))
    (is (valid? [:= [:quot a k] (quot a k)]) (str "(quot " a " " k ")"))
    (is (valid? [:=> [:= 'x a] [:and [:= [:mod 'x k] (mod a k)] [:= [:quot 'x k] (quot a k)]]])
        (str "symbolic " a " " k))))

(deftest quot-truncates
  (is (valid? [:=> [:<= 0 'x] [:<= 0 [:quot 'x 3]]]))
  (is (valid? [:=> [:<= 'x 0] [:<= [:quot 'x 3] 0]]))
  (is (valid? [:=> [:<= 'x 0] [:>= [:quot 'x -3] 0]]))
  (is (valid? [:=> [:<= 0 'x] [:= 'x [:+ [:* 4 [:quot 'x 4]] [:mod 'x 4]]]]))
  (is (invalid-model [:= 'x [:+ [:* 4 [:quot 'x 4]] [:mod 'x 4]]])))

;; --- integers, not rationals --------------------------------------------------

(deftest integer-infeasibility
  (is (unsat? [:= [:* 2 'x] 1]))
  (is (unsat? [:and [:<= 3 [:* 2 'x]] [:<= [:* 2 'x] 3]]))
  (is (unsat? [:and [:<= 1 [:- [:* 3 'x] [:* 3 'y]]] [:<= [:- [:* 3 'x] [:* 3 'y]] 2]]))
  ;; x = 3, y = 5/3 is a rational point; there is no integer one
  (is (unsat? [:and [:= [:- [:* 2 'x] [:* 3 'y]] 1] [:<= 3 'x 4]]))
  (is (sat-model [:and [:= [:+ [:* 2 'x] [:* 3 'y]] 1] [:<= 0 'x 10]])))

;; --- abs, max, min, ite ---------------------------------------------------------

(deftest abs-max-min-ite
  (is (valid? [:>= [:abs 'x] 0]))
  (is (valid? [:>= [:abs 'x] 'x]))
  (is (valid? [:= [:max 'x 'y] [:neg [:min [:neg 'x] [:neg 'y]]]]))
  (is (valid? [:= [:ite [:< 'x 0] [:neg 'x] 'x] [:abs 'x]]))
  (is (invalid-model [:= [:abs 'x] 'x])))

(deftest min-is-monotone
  (is (valid? [:=> [:<= 'a 'b] [:<= [:min 'cap [:* 2 'a]] [:min 'cap [:* 2 'b]]]]))
  (is (invalid-model [:=> [:<= 'a 'b] [:< [:min 'cap [:* 2 'a]] [:min 'cap [:* 2 'b]]]])))

(deftest doubling-until-cap
  ;; one step of x := min(cap, 2x) keeps 0 < x <= cap and never shrinks x
  (let [step [:min 'cap [:* 2 'x]]]
    (is (valid? [:=> [:and [:< 0 'x] [:<= 'x 'cap]]
                 [:and [:< 0 step] [:<= step 'cap] [:<= 'x step]]]))
    (is (valid? [:=> [:and [:< 0 'x] [:<= 'x 'cap] [:= step 'x]] [:= 'x 'cap]]))
    (is (invalid-model [:=> [:<= 'x 'cap] [:<= 'x step]]))))

;; --- uninterpreted functions ------------------------------------------------------

(deftest euf
  (let [d {'f [:fn 1] 'g [:fn 2] 'p [:pred 1]}]
    (is (valid? [:=> [:= 'x 'y] [:= [:app 'f 'x] [:app 'f 'y]]] d))
    (is (valid? [:=> [:= 'x [:+ 'y 1]] [:= [:app 'f 'x] [:app 'f [:+ 1 'y]]]] d))
    (is (valid? [:=> [:and [:= 'x 'y] [:papp 'p 'x]] [:papp 'p 'y]] d))
    (is (valid? [:=> [:and [:= 'a 'b] [:= 'c 'd]] [:= [:app 'g 'a 'c] [:app 'g 'b 'd]]] d))
    (is (valid? [:=> [:= 'x 'y] [:= [:app 'f [:app 'f 'x]] [:app 'f [:app 'f 'y]]]] d))
    (let [m (invalid-model [:=> [:= [:app 'f 'x] [:app 'f 'y]] [:= 'x 'y]] d)]
      (is m)
      (is (map? (get-in m ['f :map])))
      (is (not= (m 'x) (m 'y))))
    (is (invalid-model [:=> [:papp 'p 'x] [:papp 'p 'y]] d))))

(deftest game-of-life-shift
  ;; the live neighbours of (x-dx, y-dy) in world w are the live neighbours
  ;; of (x, y) in w shifted by (dx, dy): w'(a, b) = w(a - dx, b - dy)
  (let [d {'w [:pred 2]}
        offsets (for [i [-1 0 1] j [-1 0 1] :when (not= [i j] [0 0])] [i j])
        live (fn [a b] [:ite [:papp 'w a b] 1 0])
        in-w (into [:+] (for [[i j] offsets]
                          (live [:+ [:- 'x 'dx] i] [:+ [:- 'y 'dy] j])))
        in-w' (into [:+] (for [[i j] offsets]
                           (live [:- [:+ 'x i] 'dx] [:- [:+ 'y j] 'dy])))]
    (is (valid? [:= in-w in-w'] d))
    (is (valid? [:and [:<= 0 in-w] [:<= in-w 8]] d))
    (is (valid? [:=> [:= in-w 3] [:iff [:= in-w' 3] true]] d))
    (is (invalid-model [:= in-w 3] d))))

;; --- budget ---------------------------------------------------------------------

(deftest a-tiny-budget-gives-unknown
  (let [f [:and [:= [:+ [:* 3 'x] [:* 5 'y]] [:+ [:* 7 'z] 1]] [:> 'x 100] [:> 'y 100]
           [:distinct 'x 'y 'z 1 2 3]]
        r (s/check f {} {:budget 1})]
    (is (= :unknown (:result r)))
    (is (string? (:reason r)))))

(deftest budget-never-gives-a-wrong-answer
  (doseq [b [1 2 3 5 8 20]]
    (let [f [:and [:= [:- [:* 2 'x] [:* 3 'y]] 1] [:<= 3 'x 4]]
          r (s/check f {} {:budget b})]
      (is (contains? #{:unsat :unknown} (:result r)))
      (when (= :unsat (:result r)) (is (s/verify f {} (:certificate r)))))))

;; --- certificates ---------------------------------------------------------------

(defn- farkas-leaves [c]
  (let [acc (volatile! [])]
    (walk/postwalk (fn [x] (when (and (map? x) (:farkas x)) (vswap! acc conj x)) x) c)
    @acc))

(defn- perturb-multiplier
  "The certificate with the first Farkas multiplier increased by one."
  [c]
  (let [done (volatile! false)]
    (walk/prewalk (fn [x]
                    (if (and (not @done) (map? x) (seq (:farkas x)))
                      (do (vreset! done true)
                          (update-in x [:farkas 0 1] + 1))
                      x))
                  c)))

(defn- drop-branch
  "The certificate with its first split replaced by the split's yes branch."
  [c]
  (let [done (volatile! false)]
    (walk/prewalk (fn [x]
                    (if (and (not @done) (map? x) (:split x))
                      (do (vreset! done true) (:yes x))
                      x))
                  c)))

(defn- has-split? [c]
  (let [found (volatile! false)]
    (walk/postwalk (fn [x] (when (and (map? x) (:split x)) (vreset! found true)) x) c)
    @found))

(defn- rejected? [f decls c]
  (try (s/verify f decls c) false
       (catch clojure.lang.ExceptionInfo _ true)))

(deftest a-tampered-certificate-is-rejected
  (let [f [:and [:< 'x 'y] [:< 'y 'z] [:< 'z 'x]]
        c (:certificate (s/check f {} {}))]
    (is (s/verify f {} c))
    (is (seq (farkas-leaves c)))
    (is (rejected? f {} (perturb-multiplier c)))
    (is (rejected? [:and [:< 'x 'y] [:< 'y 'z]] {} c) "a certificate for another formula"))
  (let [f [:and [:or [:< 'x 0] [:> 'x 5]] [:<= 0 'x 5]]
        c (:certificate (s/check f {} {}))]
    (is (s/verify f {} c))
    (is (rejected? f {} (drop-branch c))))
  (let [f [:= [:* 2 'x] 1]
        c (:certificate (s/check f {} {}))]
    (is (rejected? f {} (assoc c :proof {:farkas []})))
    (is (rejected? f {} (assoc c :proof {:clause 99})))))

(deftest a-validity-certificate-says-so
  (let [f [:>= [:abs 'x] 0]
        r (s/valid? f {} {})
        c (:certificate r)]
    (is (= :valid (:claim c)))
    (is (s/verify f {} c))
    (is (rejected? [:< [:abs 'x] 0] {} c))))

;; --- random formulas against brute force ------------------------------------------

(def ^:private vars '[x y z])

(def ^:private gen-term
  (gen/recursive-gen
   (fn [inner]
     (gen/one-of
      [(gen/fmap (fn [[a b]] [:+ a b]) (gen/tuple inner inner))
       (gen/fmap (fn [[a b]] [:- a b]) (gen/tuple inner inner))
       (gen/fmap (fn [[k a]] [:* k a]) (gen/tuple (gen/choose -3 3) inner))
       (gen/fmap (fn [[a k]] [:mod a k]) (gen/tuple inner (gen/elements [-3 -2 2 3])))
       (gen/fmap (fn [[a k]] [:quot a k]) (gen/tuple inner (gen/elements [-3 -2 2 3])))
       (gen/fmap (fn [a] [:abs a]) inner)
       (gen/fmap (fn [[a b]] [:max a b]) (gen/tuple inner inner))
       (gen/fmap (fn [[a b]] [:min a b]) (gen/tuple inner inner))
       (gen/fmap (fn [[a b c]] [:ite [:< a 0] b c]) (gen/tuple inner inner inner))]))
   (gen/one-of [(gen/choose -4 4) (gen/elements vars)])))

(def ^:private gen-atom
  (gen/fmap (fn [[op a b]] [op a b])
            (gen/tuple (gen/elements [:< :<= :> :>= := :distinct]) gen-term gen-term)))

(def ^:private gen-formula
  (gen/recursive-gen
   (fn [inner]
     (gen/one-of
      [(gen/fmap (fn [ps] (into [:and] ps)) (gen/vector inner 1 3))
       (gen/fmap (fn [ps] (into [:or] ps)) (gen/vector inner 1 3))
       (gen/fmap (fn [p] [:not p]) inner)
       (gen/fmap (fn [[p q]] [:=> p q]) (gen/tuple inner inner))
       (gen/fmap (fn [[p q]] [:iff p q]) (gen/tuple inner inner))]))
   gen-atom))

(defn- brute-force
  "A model in the box [-6,6]^3, or nil."
  [f]
  (first (for [x (range -6 7) y (range -6 7) z (range -6 7)
               :let [m {'x x 'y y 'z z}]
               :when (s/eval-formula f m)]
           m)))

(defn- agrees-with-brute-force [f]
  (let [r (s/check f {} {:budget 2000})
        bf (brute-force f)]
    (case (:result r)
      :sat (s/eval-formula f (:model r))
      :unsat (and (nil? bf)
                  (s/verify f {} (:certificate r))
                  (let [c (:certificate r)]
                    (and (or (empty? (farkas-leaves c)) (rejected? f {} (perturb-multiplier c)))
                         (or (not (has-split? c)) (rejected? f {} (drop-branch c))))))
      :unknown true)))

(deftest random-formulas-agree-with-brute-force
  (let [r (tc/quick-check 400 (prop/for-all [f gen-formula] (agrees-with-brute-force f))
                          :seed 20260923 :max-size 12)]
    (is (:pass? r) (pr-str (select-keys r [:shrunk :fail])))))

(deftest random-conjunctions-agree-with-brute-force
  ;; conjunctions of atoms are unsat often, so certificates get exercised
  (let [r (tc/quick-check 400 (prop/for-all [ps (gen/vector gen-atom 2 5)]
                                (agrees-with-brute-force (into [:and] ps)))
                          :seed 7 :max-size 8)]
    (is (:pass? r) (pr-str (select-keys r [:shrunk :fail])))))
