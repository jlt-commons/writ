(ns writ.spec-demo.gate
  "A door that lets in adult members.")

(defn admit [age member?]
  (if (and (<= 18 age) member?) :in :out))

(defn holder [m id who]
  (if (and (contains? m id) (= who (:who (get m id)))) :theirs :not))

(defn badges [ages] (vec (for [a ages :when (<= 18 a)] a)))
