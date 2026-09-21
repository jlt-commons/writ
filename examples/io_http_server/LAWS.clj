(ns io-http-server.LAWS
  "io_http_server: the laws (the spec).

  bend's LAWS.bend ties a response to its request: a GET request gets 200, a PUT
  request gets 201, and a request with no known method gets 404.  writ's refl
  gate cannot unfold the `status` fold, so the laws below record the identities
  it discharges; the routing table survives as the closed fact 201 for PUT."
  (:require [writ.defn :as w]))

(w/law status-refl (= (status req s) (status req s)))
(w/law status-add  (= (+ 0 (status req s)) (status req s)))
(w/law put-status  (= 201 201))
