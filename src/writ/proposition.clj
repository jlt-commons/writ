(ns writ.proposition
  "Equivalence of propositions independently of a spec namespace."
  (:require [writ.lower :as l]))

(defn- head? [form head-name]
  (and (seq? form) (symbol? (first form)) (= head-name (name (first form)))))

(def subst-var
  "Replace free occurrences of x with e, respecting lexical binders."
  l/subst-var)

(defn canonical [prop]
  (loop [p prop bs [] i 0]
    (if (head? p "forall")
      (let [[_ [x t] body] p
            y (symbol (str "_" i))]
        (recur (subst-var body x y) (conj bs t) (inc i)))
      [bs p])))

(defn alpha= [p q]
  (= (canonical p) (canonical q)))
