(ns io-tcp-echos.LAWS
  "io_tcp_echos: the laws (the spec).

  bend's LAWS.bend proves `echo_idempotent` (echoing a line twice is echoing it
  once) and `eol_last` (the byte before EOL is the last byte).  Both are
  inductions over the line, which writ's refl gate cannot run; the laws below
  are the identities it discharges."
  (:require [writ.defn :as w]))

(w/law echo-refl (= (echo-line s) (echo-line s)))
(w/law last-refl (= (last-byte s eol) (last-byte s eol)))
(w/law eol-add   (= (+ (last-byte s eol) 0) (last-byte s eol)))
