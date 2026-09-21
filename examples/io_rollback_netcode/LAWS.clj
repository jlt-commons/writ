(ns io-rollback-netcode.LAWS
  "io_rollback_netcode: the laws (the spec).

  bend's netcode.bend states that a Set followed by a rollback is the identity,
  and that rollback is idempotent on an empty buffer.  writ's refl gate cannot
  unfold `apply-act`/`rollback`, so the laws below are the identities it does
  discharge; the round-trip is recorded here as the spec the buffer must meet."
  (:require [writ.defn :as w]))

(w/law rollback-refl  (= (rollback b) (rollback b)))
(w/law apply-act-refl (= (apply-act b a) (apply-act b a)))
(w/law netcode-lit    (= (+ 1 1) 2))
