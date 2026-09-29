(ns writ.spec-demo.slug-spec
  "The slug's laws rest on what clojure.string does, stated as
  assumptions: tested against clojure.string on every check, and cited by
  the prover as given."
  (:require [clojure.string :as str]
            [writ.spec :refer [spec ann refine graph law assume]]))

(spec writ.spec-demo.slug {:require :proved})

(assume str/trim [String -> String])
(assume str/lower-case [String -> String])

(assume trim-is-idempotent
  (forall [s String] (= (str/trim (str/trim s)) (str/trim s))))
(assume lower-case-is-idempotent
  (forall [s String] (= (str/lower-case (str/lower-case s)) (str/lower-case s))))
(assume trim-and-lower-case-commute
  (forall [s String] (= (str/trim (str/lower-case s)) (str/lower-case (str/trim s)))))
(assume trim-drops-padding
  (forall [s String] (= (str/trim (str " " s " ")) (str/trim s))))

(ann clean      [String -> String])
(ann same-slug? [String String -> Bool])

(refine Clean [s String] (= s (str/lower-case (str/trim s))))

(graph slugging
  {:states {:raw String, :clean Clean}
   :edges  {:raw {[clean] #{:clean}}}})

(law cleaning-twice-is-cleaning-once
  (forall [s String] (= (clean (clean s)) (clean s))))

(law padding-is-ignored
  (forall [s String] (= (clean (str " " s " ")) (clean s))))

(law a-string-has-its-own-slug
  (forall [s String] (same-slug? s s)))

(law different-letters-differ
  (not (same-slug? "a" "b")))

(law padded-strings-share-a-slug
  (forall [s String] (same-slug? (str " " s " ") s)))
