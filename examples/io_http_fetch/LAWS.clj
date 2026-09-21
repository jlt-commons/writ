(ns io-http-fetch.LAWS
  "io_http_fetch: the laws (the spec).

  bend's LAWS.bend states two laws about the walker.  body_after_blank: for
  every body b, body(\"\\r\\n\\r\\n\" ++ b) == b.  body_suffix: for every response
  s, the body is a suffix of s (some prefix p has p ++ body(s) == s).  Both are
  proved by induction over the text, which writ's refl gate cannot do.  The
  laws below are the identities it discharges; the real laws are stated here as
  the spec the walker exists to meet."
  (:require [writ.defn :as w]))

(w/law body-refl        (= (body s) (body s)))
(w/law window-add-zero  (= (+ (window w c) 0) (window w c)))
(w/law window-unit-left (= (+ 0 (window w c)) (window w c)))

;; the blank-line window, as a closed equation -- io_hello_world's shape, a law
;; with nothing to quantify over.
(w/law blank-closed (= 218762506 218762506))
