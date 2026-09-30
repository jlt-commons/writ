(ns writ.spec-demo.slug-cheat-spec
  "An assumption about the target itself: that would let the spec assume
  what it should check."
  (:require [clojure.string :as str]
            [writ.spec :refer [spec ann refine graph law assume]]))

(spec writ.spec-demo.slug)

(assume clean-is-idempotent (forall [s String] (= (clean (clean s)) (clean s))))

(ann clean      [String -> String])
(ann same-slug? [String String -> Bool])

(graph slugging
  {:states {:raw String, :out String}
   :edges  {:raw {[clean] #{:out}}}})

(law a-string-has-its-own-slug
  (forall [s String] (same-slug? s s)))
