(ns app-pong-game-2d.PROOF
  "app_pong_game_2d: the proofs, and the verifier."
  (:require [app-pong-game-2d.main]
            [app-pong-game-2d.LAWS]
            [writ.defn :as w]
            [writ.book :as book]))

(w/proof holds-refl-refl holds-refl refl)
(w/proof quits-refl-refl quits-refl refl)
(w/proof pong-lit-refl   pong-lit   refl)

(defn verify []
  (book/check-files
    "app_pong_game_2d/main.clj"
    "app_pong_game_2d/LAWS.clj"
    "app_pong_game_2d/PROOF.clj"))
