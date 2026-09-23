(ns writ.spec-demo.court-spec
  "The court's contract, every law proved: the prover reads the named
  constants, max and min, abs, not=, every? and some, a comparison of
  three, and contains? on a set of keywords."
  (:require [writ.spec-demo.court :refer [H PH]]
            [writ.spec :refer [spec data ann law]]))

(spec writ.spec-demo.court {:require :proved})

(data Key Idle Up Down)

(ann move     [Int Key -> Int])
(ann safe?    [Keyword -> Bool])
(ann distance [Int Int -> Nat])

(def top (- H PH))

(law a-paddle-stays-on-the-court
  (forall [y Int, k Key] (<= 0 (move y k) top)))

(law up-moves-two-rows-away-from-the-wall
  (forall [y Int] (=> (<= 2 y top) (= (move y [:Up]) (- y 2)))))

(law a-tick-moves-at-most-two-rows
  (forall [y Int, k Key] (=> (<= 0 y top) (<= (distance y (move y k)) 2))))

(law up-and-down-part-ways
  (forall [y Int] (=> (< 2 y (- top 2)) (not= (move y [:Up]) (move y [:Down])))))

(law every-key-keeps-the-paddle-on
  (forall [y Int] (every? (fn [k] (<= 0 (move y k) top)) [[:Up] [:Down] [:Idle]])))

(law some-key-moves-it-up
  (forall [y Int] (=> (<= 2 y top) (some (fn [k] (< (move y k) y)) [[:Idle] [:Up]]))))

(law safe-means-get-head-or-put
  (forall [m Keyword] (= (safe? m) (or (= m :get) (= m :head) (= m :put)))))

(law distance-is-the-gap
  (forall [a Int, b Int] (= (distance a b) (if (< a b) (- b a) (- a b)))))
