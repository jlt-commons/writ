(ns writ.spec-demo.binders
  "The names a pattern form binds: a symbol other than _ binds itself, a
  vector the names of its elements, nested.")

(defn- atom-binder [p] (if (and (symbol? p) (not= p '_)) [p] []))

(defn- tuple-binders
  [ps]
  (if (empty? ps)
    []
    (let [p (first ps)]
      (concat (if (vector? p) (tuple-binders p) (atom-binder p))
              (tuple-binders (rest ps))))))

(defn bound-syms
  "The symbols a pattern binds, in order, each once."
  [pat]
  (distinct (if (vector? pat) (tuple-binders pat) (atom-binder pat))))
