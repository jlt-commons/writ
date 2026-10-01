(ns writ.spec-demo.waitlist-spec
  "Laws over vectors of unknown length: a queue per title. The prover reads
  a queue as a slice of an array, with what is conj'd after it."
  (:require [writ.spec :refer [spec ann refine graph law]]))

(spec writ.spec-demo.waitlist)

(defn once? [w] (every? (fn [[_ q]] (= (count q) (count (distinct q)))) w))
(defn settle [w] (into {} (for [[t q] w] [t (vec (distinct q))])))

(refine Waits [w (Map Nat (Vec Nat))] (once? w) {:build settle})

(ann join    [Waits Nat Nat -> Waits])
(ann serve   [Waits Nat -> Waits])
(ann next-up [Waits Nat -> (Opt Nat)])
(ann cancel  [Waits Nat Nat -> Waits])

(graph desk {:states {:w Waits}
             :edges {:w {[join Nat Nat] #{:w} [serve Nat] #{:w} [cancel Nat Nat] #{:w}}}})

(law joining-puts-the-member-last
  (forall [w Waits, t Nat, m Nat]
    (=> (not (some #{m} (get w t [])))
        (= (conj (vec (get w t [])) m) (get (join w t m) t)))))

(law joining-again-changes-nothing
  (forall [w Waits, t Nat, m Nat]
    (=> (some #{m} (get w t [])) (= w (join w t m)))))

(law the-first-in-line-is-next
  (forall [w Waits, t Nat]
    (= (first (get w t [])) (next-up w t))))

(law serving-takes-the-first-off
  (forall [w Waits, t Nat]
    (=> (seq (get w t []))
        (= (rest (get w t [])) (get (serve w t) t)))))

(law serving-shortens-the-line-by-one
  (forall [w Waits, t Nat]
    (=> (seq (get w t []))
        (= (dec (count (get w t []))) (count (get (serve w t) t))))))

(law serving-touches-only-that-line
  (forall [w Waits, t Nat, u Nat]
    (=> (not= t u) (= (get w u) (get (serve w t) u)))))

(law cancelling-keeps-the-others-in-order
  (forall [w Waits, t Nat, m Nat]
    (=> (some #{m} (get w t []))
        (= (filter #(not= m %) (get w t [])) (get (cancel w t m) t)))))

(law a-cancelled-member-is-out
  (forall [w Waits, t Nat, m Nat]
    (not (some #{m} (get (cancel w t m) t [])))))
