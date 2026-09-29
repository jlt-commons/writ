(ns writ.spec-demo.slug-liar-spec
  "A signature for clojure.string/trim that it does not keep: the check
  runs the laws with trim wrapped, so the lie shows where trim returns."
  (:require [clojure.string :as str]
            [writ.spec :refer [spec ann refine graph law assume]]))

(spec writ.spec-demo.slug)

(assume str/trim [String -> Nat])

(ann clean      [String -> String])
(ann same-slug? [String String -> Bool])

(refine Clean [s String] (= s (str/lower-case (str/trim s))))

(graph slugging
  {:states {:raw String, :clean Clean}
   :edges  {:raw {[clean] #{:clean}}}})

(law a-string-has-its-own-slug
  (forall [s String] (same-slug? s s)))
