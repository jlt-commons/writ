(ns writ.spec-demo.slug-length-spec
  "A law only whitespace breaks: trimming shortens a padded string."
  (:require [writ.spec :refer [spec ann graph law]]))

(spec writ.spec-demo.slug {:test false})

(ann clean      [String -> String])
(ann same-slug? [String String -> Bool])

(graph slugging
  {:states {:raw String, :out String}
   :edges  {:raw {[clean] #{:out}}}})

(law cleaning-keeps-the-length
  (forall [s String] (= (count (clean s)) (count s))))
