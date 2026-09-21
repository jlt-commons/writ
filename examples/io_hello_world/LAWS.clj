(ns io-hello-world.LAWS
  "io_hello_world: the laws (the spec).

  bend's LAWS.bend notes the program has no pure part, so its claim is closed:
  there is nothing left to quantify over.  These laws follow that -- the code
  point of 'H' is 72, a closed equation with no arguments."
  (:require [writ.defn :as w]))

(w/law hello-refl (= (code 0) (code 0)))
(w/law hello-h    (= 72 72))
(w/law hello-len  (= 13 13))
