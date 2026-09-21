(ns io-http-server.main
  "io_http_server: the pure part of bend's HTTP server.

  Ported from bend's demos/io_http_server.  The demo routes each request and
  writes a status line.  The socket IO is not something writ checks; what it
  checks is the status fold, which scans a request's method codes and settles on
  201 once a PUT (code 1) appears, 200 once a GET (code 0) appears, and 404
  otherwise.  A request is a list of Nat method codes."
  (:require [writ.defn :as w]))

(w/data Req Nil (Cons Nat Req))

;; fold the request's method codes into a status, `s` being the status so far.
(w/defn ^{:writ/descend true} status [req :- Req s :- Nat] :- Nat
  (w/match req :- Req
    (Nil s)
    ((Cons ^:many c t) (status t (if (= c 1) 201 (if (= c 0) 200 s))))))
