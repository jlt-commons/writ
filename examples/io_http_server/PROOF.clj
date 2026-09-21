(ns io-http-server.PROOF
  "io_http_server: the proofs, and the verifier."
  (:require [io-http-server.main]
            [io-http-server.LAWS]
            [writ.defn :as w]
            [writ.book :as book]))

(w/proof status-refl-refl status-refl refl)
(w/proof status-add-refl  status-add  refl)
(w/proof put-status-refl  put-status  refl)

(defn verify []
  (book/check-files
    "io_http_server/main.clj"
    "io_http_server/LAWS.clj"
    "io_http_server/PROOF.clj"))
