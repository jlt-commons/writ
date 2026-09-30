(ns writ.spec-demo.slug-unused-spec
  "A signature for a fn neither the code nor the laws call, and that writ
  calls on its own: writ's calls are not the spec's to type."
  (:require [clojure.string :as str]
            [writ.spec :refer [spec ann refine graph law assume]]))

(spec writ.spec-demo.slug)

(assume str/starts-with? [Nat Nat -> Bool])

(ann clean      [String -> String])
(ann same-slug? [String String -> Bool])

(refine Clean [s String] (= s (str/lower-case (str/trim s))))

(graph slugging
  {:states {:raw String, :clean Clean}
   :edges  {:raw {[clean] #{:clean}}}})

(law a-string-has-its-own-slug
  (forall [s String] (same-slug? s s)))
