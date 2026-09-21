(ns io-hello-world.main
  "io_hello_world: the pure part of bend's hello world.

  bend's demos/io_hello_world is a single `IO.print(\"Hello, world!\")`: it
  has no pure part at all, so there is nothing of it for writ to port.  `code`
  is an invented stand-in that keeps the book non-empty: a descending,
  guarded recursion over a Nat."
  (:require [writ.defn :as w]))

;; the n-th code point of "Hello, World!", starting at 'H'.
(w/defn ^{:writ/descend true} code [^:many n :- Nat] :- Nat
  (if (zero? n) 72 (inc (code (dec n)))))
