(ns writ.spec-demo.court-open
  "court with a clamp that forgot its top: a paddle can leave the court.")

(def H 45)
(def PH 8)
(def SAFE #{:get :head :put})

(defn- clamp [lo hi v]
  (max lo v))

(defn move [y key]
  (case (first key)
    :Up (clamp 0 (- H PH) (- y 2))
    :Down (clamp 0 (- H PH) (+ y 2))
    :Idle (clamp 0 (- H PH) y)))

(defn safe? [method]
  (contains? SAFE method))

(defn distance [a b]
  (abs (- a b)))
