(ns app-slash-boss-3d.PROOF
  "app_slash_boss_3d: the proofs, and the verifier."
  (:require [app-slash-boss-3d.main]
            [app-slash-boss-3d.LAWS]
            [writ.defn :as w]
            [writ.book :as book]))

(w/proof move-up-refl-refl    move-up-refl    refl)
(w/proof move-right-refl-refl move-right-refl refl)
(w/proof slash-lit-refl       slash-lit       refl)

(defn verify []
  (book/check-files
    "app_slash_boss_3d/main.clj"
    "app_slash_boss_3d/LAWS.clj"
    "app_slash_boss_3d/PROOF.clj"))
