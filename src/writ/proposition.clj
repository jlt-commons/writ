(ns writ.proposition
  "Equivalence of propositions independently of a spec namespace."
  (:require [writ.lower :as l]))

(defn- head? [form head-name]
  (and (seq? form) (symbol? (first form)) (= head-name (name (first form)))))

(defn subst-var
  "Replace free occurrences of x with e, stopping at binders of x."
  [form x e]
  (letfn [(binds? [bs] (some #{x} (mapcat l/binding-names (take-nth 2 bs))))
          (walk [f]
            (cond
              (= x f) e
              (and (seq? f) (= 'quote (first f))) f
              (and (seq? f) (contains? '#{let let* loop loop* forall exists} (first f))
                   (vector? (second f)) (binds? (second f)))
              f
              (and (seq? f) (contains? '#{fn fn*} (first f))
                   (some #(and (vector? %) (some #{x} (mapcat l/binding-names %))) (take 3 f)))
              f
              (seq? f) (apply list (map walk f))
              (vector? f) (mapv walk f)
              (map? f) (into {} (map (fn [[k v]] [(walk k) (walk v)])) f)
              (set? f) (into #{} (map walk) f)
              :else f))]
    (walk form)))

(defn canonical [prop]
  (loop [p prop bs [] i 0]
    (if (head? p "forall")
      (let [[_ [x t] body] p
            y (symbol (str "_" i))]
        (recur (subst-var body x y) (conj bs t) (inc i)))
      [bs p])))

(defn alpha= [p q]
  (= (canonical p) (canonical q)))
