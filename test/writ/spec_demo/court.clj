(ns writ.spec-demo.court
  "A paddle on a court of fixed height, and the methods a client may send
  again.  Written with named constants, clamping through max and min, and
  a set of keywords, the forms the prover must read as they are.")

(def H 45)
(def PH 8)
(def SAFE #{:get :head :put})

(defn- clamp [lo hi v]
  (max lo (min hi v)))

(defn move [y key]
  (case (first key)
    :Up (clamp 0 (- H PH) (- y 2))
    :Down (clamp 0 (- H PH) (+ y 2))
    :Idle (clamp 0 (- H PH) y)))

(defn safe? [method]
  (contains? SAFE method))

(defn distance [a b]
  (abs (- a b)))
