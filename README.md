# writ

writ checks Clojure code against Bend's static rules. It is for constraining
LLM-generated code, not for running anything in parallel.

The surface stays Clojure. Annotations ride on ordinary metadata, and a few
macros put them in the signature when you want that.

writ enforces quantities (affinity), the kind lattice, live/dead demand,
structural descent, match discipline, the law/proof gate, and conversion.

writ is a checker only. Every macro expands to the plain form it annotates
(`w/defn` is `defn`, `w/data` and `w/law` are quoted `def`s), so checked code
runs exactly as if writ were absent: zero runtime cost, no runtime dependency.

## Quantities

- `^:many` (or `^:omega`, `^:reusable`) — reusable, may be copied
- `^:zero` (or `^:erased`) — erased, must be dropped
- no mark — affine, used exactly once

```clojure
(w/defn dup [^:many x :- Nat] (+ x x))   ; ok
(w/defn dup [x :- Nat] (+ x x))          ; rejected: x is affine and used twice
```

A reusable binder must be Data, as in Bend: a function is never copied. A
`^:many` parameter needs a Data type (`:- Nat` in `w/defn`, `^Nat` on a plain
`defn`). A `^:many` local passes when writ can infer a Data type for its
value (literals, arithmetic, typed calls, pattern binders); otherwise it
needs an annotation too.

An erased binding that is never used is fine. An erased binding that is used is
not.

```clojure
(w/defn f [^:zero ctx x] (inc x))   ; ok, ctx is dropped
(w/defn f [^:zero ctx x] ctx)       ; rejected: ctx is erased and used once
```

`if` and `case` arms join. A use in each arm counts as one use along each path.
Sequential uses add. Collection literals are walked like expressions, so a
double use inside a vector, map or set counts. Sibling scopes may reuse a
name; shadowing a parameter or binding one name twice in a form is rejected.

## Types

`:-` separates a name from its type. A leading `:-` after the parameters is the
return type.

```clojure
(w/defn add [^:many a :- Nat, b :- Nat] :- Nat
  (if (zero? a) b (add (dec a) b)))
```

Type names must be known. A type constructor takes the right number of
arguments. `Nat`, `Bool`, `Int`, `String` and the rest are built in, and
`w/data` adds your own.

## Erasure

Types are checked dead, as in Bend: an erased binder may appear in a type,
but never in running code.

```clojure
(w/defn f [^:zero x] :- Nat 0)   ; ok, x is dropped
(w/defn f [^:zero x] :- Nat x)   ; rejected: x is erased and used
```

Bend erases dead code before it runs; Clojure does not. So the value of a
`^:zero` local and an argument to a `^:zero` parameter still count as uses:
they are evaluated.

## Type variables

Generic code declares its type variables in the attr-map. They are erased by
construction (no runtime argument) and have kind Type, so a value of that type
cannot be `^:many` unless the variable is declared Data.

```clojure
(w/defn id {:writ/forall [a]} [x :- a] :- a x)
(w/defn dup {:writ/forall [a :- Data]} [^:many x :- a] [x x])
```

## Types

`:-` annotations are checked, not trusted. A call's arguments must fit the
callee's parameter types, the body must fit the return type, and a value
whose type is not a function cannot be called. Unannotated code is inferred
where writ can (literals, arithmetic, predicates, typed calls); an unknown
type never fails a check on its own. `Nat` widens to `Int`, and under a
guard like `(zero? n)` or `(pos? n)`, `(dec n)` of a `Nat` stays `Nat`.
`List`, `Vec`, `Set` and `Map` are built-in collection types; a book type of
the same name shadows them. As in Bend, a collection is as reusable as its
element: `(List Nat)` is Data, `(List (-> Nat Nat))` is not.

## Data and match

```clojure
(w/data MaybeInt Nothing (Just Int))
(w/data Box [a] (Wrap a))
```

```clojure
(w/defn from-maybe [m :- MaybeInt]
  (w/match m :- MaybeInt
    (Nothing 0)
    ((Just x) x)))
```

A match checks its discipline. The scrutinee is a parameter or a pattern
binder, not a computed value (a `let` or `loop` that rebinds the name makes
it computed), and when its type is known it must be the match type. Every
constructor appears once, patterns bind the right number of fields, and no
constructor is left out -- or a lowercase catch-all arm like `(other ...)`
or `(_ ...)` comes last and takes the rest. A type with no constructors is
matched with no arms. Pattern binders are plain symbols (`_` may repeat);
match a field again to look inside it. A field may declare its quantity,
`(w/data P (MkP ^:many Nat))`, and an unmarked binder takes it. A data
value is only taken apart by `match`: `first`, `nth` or vector
destructuring on it reads its encoding, and is rejected.

```clojure
(w/defn f [m :- MaybeInt]
  (w/match m :- MaybeInt (Nothing 0)))   ; rejected: missing Just
```

## Descent

Mark a function `^{:writ/descend true}`. Every recursive call and `recur` is
read left to right, as in Bend: each argument passes its own parameter
unchanged until one is a strict part of its own parameter (`dec`, `rest`,
`next`, `first`, `nth`, a destructured or matched field). That shrink only
counts under a test that proves it: `dec` needs `pos?`, or `zero?` on a
`Nat`; `rest` needs `seq` or `empty?`; `next` and element reads need the
value non-nil. A function's own name may appear only as a call head.
Sequences are assumed finite.

```clojure
(defn add {:writ/descend true} [^:many ^Nat a b]
  (if (zero? a) b (add (dec a) b)))   ; ok
```

## Laws and proofs

A law is a proposition. A proof discharges it. The gate fails when a law has no
proof.

```clojure
(w/law add-zero (forall [n Nat] (= (+ n 0) n)))
(w/proof add-zero-refl add-zero (fn [n] refl))
```

`refl` proves an equality only when both sides are convertible, up to
renaming binders. Normalisation does only the reductions Clojure itself
does, in its strict order: `let` and applied `fn`s whose arguments are
values, `if` and `case` on a literal, arithmetic on literals, and `(+ x 0)`
to `x`, `(* x 1)` to `x` when `x` is a number (typed by a `forall`, or a
call to a book fn returning a number). A term that throws, like `(quot 1 0)`,
equals nothing, and `=` on fns is identity, so fn values are never proved
equal. Law terms obey the book's ordering, arity and effect rules, and law
and proof names are book names.

```clojure
(w/law bad (forall [x Nat] (= (+ x 0) (inc x))))
(w/proof p bad (fn [x] refl))   ; rejected: the two sides are not convertible
```

## Data is taken apart, not built

`w/data` declares a type for the checker only; it defines no constructor
functions. A book takes data apart with `match` and never builds it: a
constructor or a type name in code is rejected. Values come from outside
the book.

## Pure code only

writ checks data-and-functions code. Host interop (`throw`, `new`, `.foo`,
`reify`, `proxy`) and effect code (`eval` and the load family, namespace and
var mutation, atoms/refs/agents, futures, I/O, randomness) are rejected,
whether written bare, as `clojure.core/x`, or through an ns alias
(`[clojure.core :as c]`). Reflection (`resolve`, `ns-publics`, `find-var`,
...) is effect code too. A book name or local with the same name shadows the
core one. Calls into other namespaces and static host calls pass through
unchecked.

A book is one namespace: a name qualified with the book's own ns (or an
alias of it, or `:refer`red from it) is a book name and obeys book order, and
a book def may not redefine a name its ns form refers in.

## Checking a book

`writ.core/check-book` takes the forms of a namespace, collects its data, laws
and proofs, checks each defn, then runs the gate. It returns `{:ok true}` or
throws.

```clojure
(require '[writ.defn :as w] '[writ.core :as writ])

(writ/check-book
  '[(w/data MaybeInt Nothing (Just Int))
    (w/defn from-maybe [m :- MaybeInt]
      (w/match m :- MaybeInt (Nothing 0) ((Just x) x)))
    (w/defn add-one [x :- Nat] :- Nat (inc x))
    (w/law add-zero (forall [n Nat] (= (+ n 0) n)))
    (w/proof add-zero-refl add-zero (fn [n] refl))])
;; => {:ok true}
```

`writ.core/check-defn` checks a single defn form on its own.

## Modules

- `writ.quant` — the quantity lattice `0 <= 1 <= w`
- `writ.ann` — the annotation vocabulary
- `writ.lower` — macroexpanded forms to a small core AST
- `writ.uses` — path-sensitive occurrence analysis
- `writ.check` — the checker (quantities, descent)
- `writ.kind` — type well-formedness
- `writ.norm` — normalisation and convertibility
- `writ.demand` — live/dead demand
- `writ.data` — data declarations
- `writ.match` — match discipline
- `writ.law` — the law/proof gate
- `writ.book` — book orchestration
- `writ.defn` — the surface macros
- `writ.core` — public entry points

## Tests

```
jolt -M:test      # or ./bin/test
```
