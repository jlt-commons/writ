(ns writ.spec-demo.verdict-shell
  "An effect shell over the verdict core: a multi-arity fn, a fn of its own
  that calls it, a macro, and alias-qualified keywords."
  (:require [writ.spec-demo.verdict :as v]
            [writ.spec-demo.verdict-core :as core]))

(defn decide
  ([kind] (decide kind :normal))
  ([kind reason] (if (v/restart? kind reason) ::restart ::core/leave)))

(defn decide-all [kinds] (mapv decide kinds))

(defmacro when-restart [kind reason & body]
  `(when (v/restart? ~kind ~reason) ~@body))
