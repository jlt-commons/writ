(ns writ.spec-demo.shadow-spec
  "A sort spec whose helper `ascending?` shares its name with a fn of the
  target.  A law must judge the code with the spec's helper, never the
  target's, so writ rejects the ambiguity instead of picking one."
  (:require [writ.spec :refer [spec ann law graph]]))

(spec writ.spec-demo.shadow)

(graph sorting {:states {:unsorted (List Nat), :sorted (List Nat)}
                :edges  {:unsorted {[isort] #{:sorted}}}})

(ann isort [(List Nat) -> (List Nat)])

(defn ascending? [xs] (or (empty? xs) (apply <= xs)))
(defn occurrences [x xs] (count (filter #(= x %) xs)))

(law sorted (forall [xs (List Nat)] (ascending? (isort xs))))
(law permutation (forall [x Nat, xs (List Nat)]
                   (= (occurrences x (isort xs)) (occurrences x xs))))
