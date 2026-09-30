(ns writ.spec-demo.tag
  "Names for keywords, and a list that grows by one.")

(defn label [k] (name k))

(defn total [items] (count items))

(defn add-item [items x] (conj (vec items) x))
