(ns writ.spec-demo.index-user-alone-spec
  (:require [writ.spec :refer [spec data ann law graph]]
            [writ.spec-demo.index-user :refer [find-k]]))

(spec writ.spec-demo.index-user )

(data Scan (Take Nat) (None Nat))

(ann find-k [(Vec Any) Any -> Scan])

(graph finding {:states {:xs (Vec Any), :r Scan} :edges {}})

(law a-find-is-a-match
  (forall [xs (Vec Any), k Any]
    (or (= :None (first (find-k xs k))) (= k (nth xs (second (find-k xs k)))))))

(law find-k-example (= (find-k [:a :b :a] :b) [:Take 1]))
