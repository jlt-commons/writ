(ns writ.spec-demo.index-spec
  (:require [writ.spec :refer [spec data ann law graph]]
            [writ.spec-demo.index :refer [scan tally]]))

(spec writ.spec-demo.index)

(data Scan (Take Nat) (None Nat))

(ann scan [(Vec Any) Any Nat -> Scan])
(ann tally [(Vec Any) Any Nat -> Nat])

(graph search {:states {:xs (Vec Any), :r Scan} :edges {}})

(law a-take-is-a-match
  (forall [xs (Vec Any), k Any, start Nat]
    (let [r (scan xs k start)]
      (or (= :None (first r)) (= k (nth xs (second r)))))))

(law a-scan-stops-at-the-end
  (forall [xs (Vec Any), k Any, start Nat]
    (=> (= :None (first (scan xs k start)))
        (= (second (scan xs k start)) (max start (count xs))))))

(law what-a-scan-steps-over-is-not-k
  (forall [xs (Vec Any), k Any, start Nat, j Nat]
    (=> (and (<= start j) (< j (second (scan xs k start))))
        (not= k (nth xs j)))))

(law a-tally-is-at-most-what-is-left
  (forall [xs (Vec Any), k Any, i Nat]
    (<= (tally xs k i) (max 0 (- (count xs) i)))))

(law a-tally-counts-from-its-index
  (and (= (tally [:a :b :a] :a 0) 2) (= (tally [:a :b :a] :a 1) 1)))
