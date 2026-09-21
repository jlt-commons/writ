(ns io-tcp-echos.PROOF
  "io_tcp_echos: the proofs, and the verifier."
  (:require [io-tcp-echos.main]
            [io-tcp-echos.LAWS]
            [writ.defn :as w]
            [writ.book :as book]))

(w/proof echo-refl-refl echo-refl refl)
(w/proof last-refl-refl last-refl refl)
(w/proof eol-add-refl   eol-add   refl)

(defn verify []
  (book/check-files
    "io_tcp_echos/main.clj"
    "io_tcp_echos/LAWS.clj"
    "io_tcp_echos/PROOF.clj"))
