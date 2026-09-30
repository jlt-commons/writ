(ns writ.spec-demo.dashes-spec
  "Assumes clojure.core's replace, which the target does not call: its
  `replace` is clojure.string's."
  (:require [clojure.string :as str]
            [writ.spec :refer [spec ann refine graph law assume]]))

(spec writ.spec-demo.dashes)

(assume clojure.core/replace [(Map Nat Nat) (List Nat) -> (List Nat)])
(assume str/replace [String String String -> String])

(ann dashes [String -> String])

(refine Dashed [s String] (not (str/includes? s " ")))

(graph dashing
  {:states {:raw String, :dashed Dashed}
   :edges  {:raw {[dashes] #{:dashed}}}
   :final  [:dashed]})

(law same-length (forall [s String] (= (count s) (count (dashes s)))))
