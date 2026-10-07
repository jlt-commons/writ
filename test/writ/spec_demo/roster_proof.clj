(ns writ.spec-demo.roster-proof
  "How writ.spec-demo.roster-spec is proved."
  (:require [writ.spec :refer [proof-of hint]]))

(proof-of writ.spec-demo.roster-spec)

(hint a-child-present-has-an-index {:induct cs :vary [i]})
