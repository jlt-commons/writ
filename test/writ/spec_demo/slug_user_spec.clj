(ns writ.spec-demo.slug-user-spec
  (:require [writ.spec :refer [spec ann graph refine law]]
            [writ.spec-demo.slug :as slug]))

(spec writ.spec-demo.slug-user {:require :proved
                                :uses [writ.spec-demo.slug-spec]})

(ann answer [String -> String])

(refine Clean [s String] (= s (slug/clean s)))

(graph answering
  {:states {:raw String, :clean Clean}
   :edges {:raw {[answer] #{:clean}}}})

(law answering-is-idempotent
  (forall [s String] (= (answer (answer s)) (answer s))))

(law answering-thrice-is-idempotent
  (forall [s String] (= (answer (answer (answer s))) (answer s))))
