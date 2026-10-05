(ns writ.spec-demo.gate
  "A door that lets in adult members.")

(defn admit [age member?]
  (if (and (<= 18 age) member?) :in :out))
