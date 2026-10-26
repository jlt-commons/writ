(ns writ.lower-test
  (:require [clojure.test :refer [deftest is testing]]
            [writ.lower :as l]))

(deftest binding-names-covers-destructuring
  (is (= '[a m] (l/binding-names '{:keys [a] :as m :or {a 1}})))
  (is (= '[x y z] (l/binding-names '{x :x [y] :ys {:keys [z]} :nested})))
  (is (= '[a xs all] (l/binding-names '[a & xs :as all])))
  (is (= '[a b c] (l/binding-names '{:foo/keys [a] :strs [b] :syms [c]}))))

(deftest transform-free-respects-sequential-bindings
  (let [f (fn [s] (if (= 'x s) 'z s))]
    (is (= '(let [x z y x] [x y])
           (l/transform-free '(let [x x y x] [x y]) #{} f)))
    (is (= '(loop [x z y x] [x y])
           (l/transform-free '(loop [x x y x] [x y]) #{} f)))))

(deftest transform-free-respects-function-quote-and-quantifier-scope
  (let [f (fn [s] (if (contains? '#{f x g} s) 'z s))]
    (is (= '(fn f [x] (z f x))
           (l/transform-free '(fn f [x] (g f x)) #{} f)))
    (is (= '(fn f [x] (g f x))
           (l/transform-free '(fn f [x] (g f x)) #{'g} f)))
    (is (= '(quote x) (l/transform-free '(quote x) #{} f)))
    (is (= '(forall [x z] (= x x))
           (l/transform-free '(forall [x x] (= x x)) #{} f)))))

(deftest substitution-stops-at-but-not-before-a-shadowing-binder
  (is (= '(let [x _0] x)
         (l/subst-var '(let [x x] x) 'x '_0)))
  (is (= '(forall [x Nat] (let [x x] x))
         (l/subst-var '(forall [x Nat] (let [x x] x)) 'x '_0))))
