(ns writ.spec-demo.nat-chain
  "Recursion two steps down a Nat: through a chain of decs, each guarded at
  its own depth, and through subtraction of a literal under a comparison.")

(defn half [n]
  (if (zero? n)
    0
    (let [m (dec n)]
      (if (zero? m) 0 (inc (half (dec m)))))))

(defn parity [n]
  (cond (zero? n) 0
        (zero? (dec n)) 1
        :else (parity (dec (dec n)))))

(defn half-by-two [n]
  (if (< n 2) 0 (inc (half-by-two (- n 2)))))

(defn thirds [n]
  (if (>= n 3) (inc (thirds (- n 3))) 0))
