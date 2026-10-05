(ns writ.spec-demo.calc-spec
  "An expression's :add has two parts; an instruction's has none: one
  name, two types, a literal typed by the fields it has."
  (:require [writ.spec :refer [spec data ann law graph]]))

(spec writ.spec-demo.calc)

(data Expr (num Int) (add Expr Expr) (neg Expr))
(data Instr (push Int) (add) (neg))

(ann compile-expr [Expr -> (Vec Instr)])

(graph g {:states {:expr Expr, :prog (Vec Instr)} :edges {:expr {[compile-expr] #{:prog}}}})

(law a-number-is-pushed (forall [n Int] (= [[:push n]] (compile-expr [:num n]))))

(law a-sum-adds-last
  (forall [a Expr, b Expr]
    (= (compile-expr [:add a b]) (conj (into (compile-expr a) (compile-expr b)) [:add]))))

(law a-program-ends-in-its-operator
  (forall [a Expr] (= [:neg] (peek (compile-expr [:neg a])))))
