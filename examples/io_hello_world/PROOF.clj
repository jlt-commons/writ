(ns io-hello-world.PROOF
  "io_hello_world: the proofs, and the verifier."
  (:require [io-hello-world.main]
            [io-hello-world.LAWS]
            [writ.defn :as w]
            [writ.book :as book]))

(w/proof hello-refl-refl hello-refl refl)
(w/proof hello-h-refl    hello-h    refl)
(w/proof hello-len-refl  hello-len  refl)

(defn verify []
  (book/check-files
    "io_hello_world/main.clj"
    "io_hello_world/LAWS.clj"
    "io_hello_world/PROOF.clj"))
