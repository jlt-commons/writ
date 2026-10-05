(ns writ.spec-demo.arith-spec
  "Expressions as tagged data: laws the prover proves by reading a
  constructor's fields off a value its contract says is an Expr, ruling
  out every tag but one, and comparing a value with a constructor field
  by field."
  (:require [writ.spec :refer [spec data ann law graph]]))

(spec writ.spec-demo.arith {:require :proved})

(data Expr (num Int) (var Keyword) (add Expr Expr) (mul Expr Expr) (neg Expr))

(ann evaluate  [Expr (Map Keyword Int) -> Int])
(ann simplify  [Expr -> Expr])
(ann size      [Expr -> Nat])
(ann variables [Expr -> (Vec Keyword)])

(graph g {:states {:expr Expr :value Int :count Nat :names (Vec Keyword)}
          :edges {:expr {[evaluate (Map Keyword Int)] #{:value} [simplify] #{:expr}
                         [size] #{:count} [variables] #{:names}}}})

(law evaluate-add
  (forall [a Expr, b Expr, env (Map Keyword Int)]
    (= (evaluate [:add a b] env) (+ (evaluate a env) (evaluate b env)))))

(law evaluate-mul
  (forall [a Expr, b Expr, env (Map Keyword Int)]
    (= (evaluate [:mul a b] env) (* (evaluate a env) (evaluate b env)))))

(law times-zero-is-zero (forall [x Expr] (= (simplify [:mul [:num 0] x]) [:num 0])))

(law plus-zero-is-itself (forall [x Expr] (= (simplify [:add [:num 0] x]) (simplify x))))

(law two-negations-cancel (forall [x Expr] (= (simplify [:neg [:neg x]]) (simplify x))))

(law size-add (forall [a Expr, b Expr] (= (size [:add a b]) (+ 1 (size a) (size b)))))

(law simplifying-keeps-the-value
  (forall [e Expr, env (Map Keyword Int)]
    (= (evaluate (simplify e) env) (evaluate e env))))

;; --- simplify is idempotent: two invariant lemmas, then the law ---------------

(defn num-of? [e n] (and (= :num (first e)) (= n (second e))))

(defn simplified?
  "No rule of simplify applies anywhere in e."
  [e]
  (case (first e)
    :num true
    :var true
    :add (let [[_ a b] e]
           (and (simplified? a) (simplified? b)
                (not (and (= :num (first a)) (= :num (first b))))
                (not (num-of? a 0)) (not (num-of? b 0))))
    :mul (let [[_ a b] e]
           (and (simplified? a) (simplified? b)
                (not (and (= :num (first a)) (= :num (first b))))
                (not (num-of? a 1)) (not (num-of? b 1))
                (not (num-of? a 0)) (not (num-of? b 0))))
    :neg (let [[_ a] e]
           (and (simplified? a) (not= :num (first a)) (not= :neg (first a))))))

(law simplify-makes-a-normal-form (forall [e Expr] (simplified? (simplify e))))

(law simplify-leaves-a-normal-form (forall [e Expr] (=> (simplified? e) (= (simplify e) e))))

(law simplifying-twice-is-simplifying-once (forall [e Expr] (= (simplify (simplify e)) (simplify e))))
