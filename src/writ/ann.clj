(ns writ.ann
  "The annotation vocabulary.

  Quantities ride on ordinary Clojure metadata, so annotated code stays plain
  Clojure:

    (defn add [^:many a b] ...)          ; a may be reused, b is affine
    (defn f [^:zero ctx x] ...)          ; ctx is erased, x is affine
    (defn g [^{:q :omega} a] ...)        ; the explicit form

  A plain parameter is affine (used exactly once).  `^:many` (or `^:omega`,
  `^:reusable`) marks it reusable; `^:zero` (or `^:erased`) marks it erased."
  (:require [writ.quant :as q]))

(defn- norm [x]
  (cond
    (contains? #{:omega :reusable :many :w} x) :w
    (contains? #{:affine :once :1} x)          :1
    (contains? #{:zero :erased :0} x)          :0
    :else nil))

(defn quantity-of
  "The quantity a symbol's metadata declares, defaulting to affine (:1)."
  [sym]
  (let [m (meta sym)
        explicit (or (:writ/q m) (:q m))
        shorthand (cond (:many m) :w
                        (:reusable m) :w
                        (:omega m) :w
                        (:zero m) :0
                        (:erased m) :0
                        (:once m) :1
                        (:affine m) :1)]
    (or (norm explicit) (norm shorthand) q/q1)))

(defn quantity? [x] (q/quant? x))

(defn qname
  "Render a quantity for error messages."
  [x]
  (case x
    :0 "erased (^:zero)"
    :1 "affine (used once)"
    :w "reusable (^:many)"
    (str x)))
