(ns writ.uses
  "Path-sensitive occurrence analysis.

  The AST has been uniquified (writ.lower/uniquify), so every binder owns a
  distinct name and a flat walk is scope-correct.  Sequential composition
  ADDs (two uses in a row is two uses); branches JOIN (a use in each arm of
  an `if` is one use per path).  This generalises the rule that a match's
  arms join to Clojure's `if`/`case`."
  (:require [writ.quant :as q]))

(defn- combine [f m1 m2]
  (let [ks (into #{} (concat (keys m1) (keys m2)))]
    (into {} (keep (fn [k]
                     (let [r (f (get m1 k q/q0) (get m2 k q/q0))]
                       (when (not= r q/q0) [k r]))))
          ks)))

(defn- addm [m1 m2] (combine q/add m1 m2))
(defn- joinm [m1 m2] (combine q/join m1 m2))

(declare uses)

(defn- uses-seq [tracked forms]
  (reduce addm {} (map (fn [f] (uses tracked f)) forms)))

(defn uses
  "Map of tracked-name -> quantity (path-joined) of how NAME is used in AST."
  [tracked ast]
  (case (:op ast)
    :ref (if (contains? tracked (:name ast)) {(:name ast) q/q1} {})
    :lit {}
    :if (addm (uses tracked (:test ast))
              (joinm (uses tracked (:then ast)) (uses tracked (:else ast))))
    :do (addm (reduce addm {} (map (fn [f] (uses tracked f)) (:stmts ast)))
              (uses tracked (:ret ast)))
    ;; fn params shadow inside their body, but outer uses inside still count:
    ;; quantity checks run per-binder, so a body use is the binder's use
    :fn (uses tracked (:body ast))
    :invoke (addm (uses tracked (:fn ast)) (uses-seq tracked (:args ast)))
    :recur (uses-seq tracked (:args ast))
    :case (addm (uses tracked (:scrut ast))
                (reduce joinm {}
                        (cond-> (mapv (fn [c] (uses tracked (:body c))) (:clauses ast))
                          (:default ast) (conj (uses tracked (:default ast))))))
    :loop (addm (uses-seq tracked (map second (:bindings ast))) (uses tracked (:body ast)))
    :let (addm (uses-seq tracked (map second (:bindings ast))) (uses tracked (:body ast)))
    :vec (uses-seq tracked (:items ast))
    :set (uses-seq tracked (:items ast))
    :map (addm (uses-seq tracked (:keys ast)) (uses-seq tracked (:vals ast)))
    {}))
