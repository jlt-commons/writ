(ns writ.spec-demo.nan-spec
  "Laws over values that may be NaN: with same, a NaN is the same as a
  NaN; with =, a law over them would be false."
  (:require [writ.spec :refer [spec ann law graph same]]))

(spec writ.spec-demo.nan {:require :proved})

(ann wrap [Any! -> (Vec Any!)])
(ann tag [Keyword Any! -> (Vec Any!)])

(graph passing {:states {:x Any!} :edges {}})

(law a-wrap-holds-its-value
  (forall [x Any!] (same (wrap x) [:v x])))

(law a-tag-keeps-its-value
  (forall [k Keyword, x Any!] (same (second (tag k x)) x)))

(law a-wrapped-nan-is-the-same-as-one (same (wrap ##NaN) [:v ##NaN]))

(law a-wrapped-nan-is-not-equal-to-one (not (= (wrap ##NaN) [:v ##NaN])))
