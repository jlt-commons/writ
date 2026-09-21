(ns io-tcp-echos.main
  "io_tcp_echos: the pure part of bend's TCP echo server.

  Ported from bend's demos/io_tcp_echos.  The demo accepts connections and
  echoes each line back.  The socket IO is not something writ checks; what it
  checks is the pure byte walker `echo-line`, which copies a line byte for byte,
  and `last-byte`, which remembers the final byte read.  A line is a list of Nat
  bytes: `:Nil`, or `[:Cons b t]`."
  (:require [writ.defn :as w]))

(w/data Text Nil (Cons Nat Text))

;; echo a line: copy it byte for byte.
(w/defn ^{:writ/descend true} echo-line [s :- Text] :- Text
  (w/match s :- Text
    (Nil :Nil)
    ((Cons c t) [:Cons c (echo-line t)])))

;; the last byte read, or `eol` when the line is empty.
(w/defn ^{:writ/descend true} last-byte [s :- Text eol :- Nat] :- Nat
  (w/match s :- Text
    (Nil eol)
    ((Cons c t) (last-byte t c))))
