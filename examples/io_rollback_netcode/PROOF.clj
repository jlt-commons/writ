(ns io-rollback-netcode.PROOF
  "io_rollback_netcode: the proofs, and the verifier."
  (:require [io-rollback-netcode.main]
            [io-rollback-netcode.LAWS]
            [writ.defn :as w]
            [writ.book :as book]))

(w/proof rollback-refl-pf    rollback-refl  refl)
(w/proof apply-act-refl-refl apply-act-refl refl)
(w/proof netcode-lit-refl    netcode-lit    refl)

(defn verify []
  (book/check-files
    "io_rollback_netcode/main.clj"
    "io_rollback_netcode/LAWS.clj"
    "io_rollback_netcode/PROOF.clj"))
