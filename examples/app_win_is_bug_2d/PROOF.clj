(ns app-win-is-bug-2d.PROOF
  "app_win_is_bug_2d: the proofs, and the verifier."
  (:require [app-win-is-bug-2d.main]
            [app-win-is-bug-2d.LAWS]
            [writ.defn :as w]
            [writ.book :as book]))

(w/proof population-refl-refl population-refl refl)
(w/proof population-unit-refl population-unit refl)
(w/proof win-lit-refl         win-lit         refl)

(defn verify []
  (book/check-files
    "app_win_is_bug_2d/main.clj"
    "app_win_is_bug_2d/LAWS.clj"
    "app_win_is_bug_2d/PROOF.clj"))
