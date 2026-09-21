(ns io-http-fetch.main
  "io_http_fetch: the pure part of bend's HTTP client.

  Ported from bend's demos/io_http_fetch.  The demo's IO -- connect, send,
  recv -- is not something writ checks.  What it checks is the pure walker
  `body`, which scans a response for its first blank line and returns the
  bytes after it.  The walker carries the last four bytes it has read as a
  big-endian Nat (a window), so it is ordinary structural recursion.

  A bend String is a list of code points; here the response is a list of Nat
  bytes, read by writ's constructor patterns: `:Nil`, or `[:Cons b t]`."
  (:require [writ.defn :as w]))

;; the blank line "\r\n\r\n" as a big-endian word: 0x0d0a0d0a.
(def blank 218762506)

;; A response: a list of bytes.
(w/data Text Nil (Cons Nat Text))

;; the window after reading byte c: w * 256 + c.
(w/defn window [w :- Nat c :- Nat] :- Nat
  (+ (* w 256) c))

;; walk the text; `e` records that the window has already matched.
(w/defn ^{:writ/descend true} body-go [s :- Text e :- Bool w :- Nat] :- Text
  (w/match s :- Text
    (Nil :Nil)
    ((Cons c t)
      (if e
        [:Cons c t]
        (let [^:many w2 (window w c)]
          (body-go t (= w2 blank) w2))))))

;; the body of a response: the bytes after its first blank line.
(w/defn body [s :- Text] :- Text
  (body-go s false 0))
