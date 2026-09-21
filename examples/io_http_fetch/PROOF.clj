(ns io-http-fetch.PROOF
  "io_http_fetch: the proofs, and the verifier."
  (:require [io-http-fetch.main]
            [io-http-fetch.LAWS]
            [writ.defn :as w]
            [writ.book :as book]))

(w/proof body-refl-refl        body-refl        refl)
(w/proof window-add-zero-refl  window-add-zero  refl)
(w/proof window-unit-left-refl window-unit-left refl)
(w/proof blank-closed-refl     blank-closed     refl)

(defn verify []
  (book/check-files
    "io_http_fetch/main.clj"
    "io_http_fetch/LAWS.clj"
    "io_http_fetch/PROOF.clj"))
