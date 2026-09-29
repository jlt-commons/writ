(ns writ.spec-demo.slug-bare-spec
  "The slug spec with no assumptions: clojure.string is outside the
  prover, so its laws are only tested."
  (:require [clojure.string :as str]
            [writ.spec :refer [spec ann refine graph law]]))

(spec writ.spec-demo.slug)

(ann clean      [String -> String])
(ann same-slug? [String String -> Bool])

(refine Clean [s String] (= s (str/lower-case (str/trim s))))

(graph slugging
  {:states {:raw String, :clean Clean}
   :edges  {:raw {[clean] #{:clean}}}})

(law cleaning-twice-is-cleaning-once
  (forall [s String] (= (clean (clean s)) (clean s))))

(law a-string-has-its-own-slug
  (forall [s String] (same-slug? s s)))

(law different-letters-differ
  (not (same-slug? "a" "b")))
