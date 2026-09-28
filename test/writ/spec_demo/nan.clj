(ns writ.spec-demo.nan
  "Code that passes values through, NaN among them.")

(defn wrap
  "x under a :v tag."
  [x]
  [:v x])

(defn tag
  "x in a tagged vector."
  [k x]
  [k x])
