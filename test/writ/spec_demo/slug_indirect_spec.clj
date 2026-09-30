(ns writ.spec-demo.slug-indirect-spec
  "An assumption about the target through a helper of the spec's own."
  (:require [clojure.string :as str]
            [writ.spec-demo.slug :as slug]
            [writ.spec :refer [spec ann refine graph law assume]]))

(spec writ.spec-demo.slug)

(defn cl [s] (slug/clean s))

(assume cl-is-idempotent (forall [s String] (= (cl (cl s)) (cl s))))

(ann clean      [String -> String])
(ann same-slug? [String String -> Bool])

(graph slugging
  {:states {:raw String, :out String}
   :edges  {:raw {[clean] #{:out}}}})

(law a-string-has-its-own-slug
  (forall [s String] (same-slug? s s)))
