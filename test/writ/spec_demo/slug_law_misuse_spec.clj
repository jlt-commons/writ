(ns writ.spec-demo.slug-law-misuse-spec
  "A law that calls an assumed fn outside its signature."
  (:require [clojure.string :as str]
            [writ.spec :refer [spec ann refine graph law assume]]))

(spec writ.spec-demo.slug)

(assume str/upper-case [Nat -> String])

(ann clean      [String -> String])
(ann same-slug? [String String -> Bool])

(refine Clean [s String] (= s (str/lower-case (str/trim s))))

(graph slugging
  {:states {:raw String, :clean Clean}
   :edges  {:raw {[clean] #{:clean}}}})

(law a-string-has-its-own-slug
  (forall [s String] (same-slug? s s)))

(law upper-then-clean-is-clean
  (forall [s String] (= (clean s) (clean (str/upper-case s)))))
