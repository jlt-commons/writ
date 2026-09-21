(ns io-rollback-netcode.main
  "io_rollback_netcode: the pure part of bend's rollback netcode.

  Ported from bend's demos/io_rollback_netcode.  The demo keeps a rollback
  buffer of inputs so a mispredicted frame can be rewound.  What writ checks is
  that buffer: `apply-act` pushes a Set onto it, `rollback` pops the last Set
  back off, and an empty buffer stays empty."
  (:require [writ.defn :as w]))

;; the buffer of Set values, newest on top.
(w/data Buf Empty (Push Nat Buf))

;; an input action: nothing, or set the value.
(w/data Act Noop Set-act)

;; perform an action, pushing a Set onto the buffer.
(w/defn apply-act [b :- Buf a :- Act] :- Buf
  (w/match a :- Act
    (Noop b)
    (Set-act b)))

;; undo the last Set by popping it; an empty buffer stays empty.
(w/defn rollback [b :- Buf] :- Buf
  (w/match b :- Buf
    (Empty :Empty)
    ((Push v t) t)))
