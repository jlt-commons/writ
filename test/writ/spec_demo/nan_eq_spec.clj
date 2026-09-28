(ns writ.spec-demo.nan-eq-spec
  "A law that compares values that may be NaN with =: false at a NaN."
  (:require [writ.spec :refer [spec ann law graph]]))

(spec writ.spec-demo.nan)

(ann wrap [Any! -> (Vec Any!)])
(ann tag [Keyword Any! -> (Vec Any!)])

(graph passing {:states {:x Any!} :edges {}})

(law a-wrap-holds-its-value
  (forall [x Any!] (= (wrap x) [:v x])))

(law a-tag-keeps-its-value
  (forall [k Keyword, x Any!] (= (second (tag k x)) x)))
