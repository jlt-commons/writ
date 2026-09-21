---
name: writ
description: Use when writing, annotating, or reviewing Clojure that is checked by writ, the zero-dependency jolt static checker for Bend's rules. Also when writing LAWS.clj / PROOF.clj spec files or example books, or when fixing any "Writ:" compile error (quantities, termination, descent, kinds, match discipline, law gate, def ordering).
---

# writ

writ checks ordinary Clojure against Bend's static rules. It is a library, not
a language. Annotations ride on metadata, every `w/...` macro expands to a
plain `clojure.core` form, and the checks run at compile time, so a rejection
is a compile error starting with `Writ:`. It runs on jolt (Clojure on Scheme,
no JVM) and has no dependencies.

## The surface

```clojure
(ns my.app
  (:require [writ.defn :as w]))

(w/data NatList Nil (Cons Nat NatList))

(w/defn ^{:writ/descend true} sum [xs :- NatList] :- Nat
  (w/match xs :- NatList
    (Nil 0)
    ((Cons h t) (+ h (sum t)))))
```

- `w/defn` is `defn` plus annotations. `:-` separates a name from its type,
  and a leading `:- Type` after the parameters is the return type.
- Quantities ride on metadata. Unmarked is affine, so at most one use (zero
  uses is fine, that is weakening). `^:many` (or `^:omega`, `^:reusable`) is
  reusable. `^:zero` (or `^:erased`) is erased and must never be used.
  `^{:q :omega}` is the explicit form.
- `(w/data Name [type-params?] Ctor (Ctor2 Field ...) ...)` declares a type.
  Ground types are built in: Nat Bool Unit Int String Char Float Double
  Keyword Symbol Any. Built-in type constructors: `(List T)`, `(Tuple T ...)`
  and `(& T ...)`, the last being a multi-value return.
- `w/match` arms pair a pattern with a body. A nullary constructor is bare,
  `(Nil body)`. A valued one binds its fields, `((Cons h t) body)`. Values are
  `[:Ctor f1 f2]` vectors.

## The rules

**Quantities cover every binder.** Parameters, `let` and `loop` locals, `fn`
parameters and pattern binders all carry a quantity. A value reached twice
needs `^:many` on the binder it flows from: `(let [^:many h (f x)] (+ h h))`,
`((Cons ^:many c t) ...)`. A local may not shadow a parameter, and one
pattern cannot bind one name for two fields. Branches join, so a use in each
`if`/match arm is one use per path. Sequential uses add. Collection literals
(`[...]`, `{...}`, `#{...}`) are walked like any expression, so a double use
inside one counts. Sibling scopes may reuse a name (two `fn`s may each bind
`t`); only shadowing a parameter or duplicating within one form is rejected.

**Termination is mandatory.** Any recursion, `loop`/`recur` included, needs
`^{:writ/descend true}` on the defn. Arguments are read left to right: each
passes its OWN column unchanged until one is a strict part of its own
column (destructured, matched, or `dec`/`rest`/`next`/`first`/`nth`/2-arg
`get` of it). A shrink counts only under a test on that column: `dec` needs
`pos?` (any integer) or `zero?`/`(= x 0)` on a `Nat`; `rest`/`drop` need
`seq`/`empty?`; `next` and element reads need it non-nil (truthiness,
`some?`, a `w/match` arm). A lookup with a default is not a shrink, and a
book fn named `dec` is not `dec`. The fn's own name may appear only as a
call head. `recur` is judged against its own loop frame. Accumulators ride
after the shrinking argument. `recur` must be in tail position,
and a defn body is an implicit loop: a tail `recur` there rebinds the
parameters, so a parameter that both feeds a test and rides into the `recur`
carries `^:many`, like a loop local.

**Defs reference earlier defs only.** No forward references and no mutual
recursion — in calls AND value positions. Qualified symbols, `clojure.core`
names, `:refer`'d names and
local `fn`s are external, not book-local, so they are fine.

**Kinds make reuse sound.** A `^:many` binder needs a type of kind Data,
proven: a `^:many` param carries a Data annotation (`:- Nat`, or `^Nat` on a
plain defn), a `^:many` local an annotation or an init whose type writ infers
as Data. `Any`, type parameters and unknown names are not Data. A closure
capturing an affine binder cannot be passed to a core higher-order fn
(`map`, `reduce`, ...), and an overlapping destructure (`{a :a b :a}`, `:as`
beside fields) copies its source, so the source must be `^:many`. A
function type is Type. A datatype with a function field anywhere is Type,
transitively, and kind flows through type parameters: `(Box Nat)` is Data,
`(Box (-> Nat Nat))` is Type.

**Data is taken apart, not built.** A constructor or a datatype name in
code is rejected (`w/data` defines no constructor fns); values come from
outside the book and are consumed by `match`. `:-` annotations work inside
`fn` params too, and a param's type may name only earlier params.

**Match discipline.** The scrutinee must be a parameter, a pattern binder or
an `fn` parameter, never a computed value or a `let` local (a let/loop/
when-let/for... that rebinds the name takes it out of scope). A known
scrutinee type must equal the match type. The type is a declared name or a
parametric application like `(Box Nat)`. Every constructor appears exactly
once and each pattern binds that constructor's field count, unless a
lowercase catch-all arm (`(x ..)`, `(_ ..)`) comes last. Pattern binders are
symbols (`_` may repeat); nest a second match to look deeper. A field's
declared quantity (`(MkP ^:many Nat)`, `^:zero`) is the binder's default.
An empty type is matched with no arms. `first`/`nth`/destructuring on a
data-typed value is rejected: take it apart with `match`.

**Erasure and type variables.** Types are checked dead (BendTT 2.4), so an
erased binder may appear in a type but not in running code. Clojure has no
erasure, so a `^:zero` local's init and an argument to a `^:zero` param still
run and still count. Generic defns declare type variables in the attr-map,
`{:writ/forall [a, b :- Data]}`: no runtime argument, kind Type unless
declared Data.

**The law gate.** A law states a proposition over `=`, `and`, `=>`, `forall`
and `exists`. A proof discharges it with `refl`, `(pair p ...)`, `(fn [h] body)`
for `=>` and `forall`, or `(witness t pf)` for `exists`. Shapes are exact:
`(= a b)`, `(=> P Q)`, `(forall [x T] P)`. `refl` holds when both sides are
convertible up to alpha: `let`/applied `fn` on value arguments (strict: a
throwing init is never dropped), `if`/`case` on a literal, arithmetic and
comparison on literals, and `(+ x 0)`/`(* x 1)` only when `x` is a number
(a `forall [x Nat]` binder, or a call to a book fn returning a number). A
throwing term equals nothing; fn values are never refl-equal. Law terms are
name/arity/effect checked like code and may not loop. A witness must fit its
domain. There is no induction and nothing about your own functions. Every law is
discharged by exactly one proof, a law may be cited as a lemma only after its
own proof, and a proof is never citable.

## Books: main, LAWS, PROOF

Keep implementation and spec apart, one directory per book:

- `main.clj` holds the implementation (`w/data`, `w/defn`).
- `LAWS.clj` holds the laws (`w/law` only, no implementation).
- `PROOF.clj` holds the proofs plus a `verify` that runs the whole book:

```clojure
(defn verify []
  (writ.book/check-files
    "my/app/main.clj"
    "my/app/LAWS.clj"
    "my/app/PROOF.clj"))
```

It returns `{:ok true}` or throws. `examples/theory_discipline` exercises the
whole rule surface in one book, and `examples/README.md` describes the rest.

## Running

In your own project, add `writ/writ` to `:deps` and require `writ.defn`. The
checks fire when the macros expand, so requiring the namespace is the check.

In this repo:

```sh
rm -rf ~/.jolt/aot-cache .jolt   # the AOT cache can serve stale namespaces
jolt -M:test                      # engine suite
cd examples && jolt -M:test       # every book, end to end
```

When a test run disagrees with a direct `jolt -e` of the same code, clear the
AOT cache before debugging the code. That is a known jolt issue, not a writ
bug.

## Fixing rejections

- `` `f` is recursive: mark it ^{:writ/descend true} `` - add the attr map, or
  rewrite without recursion.
- ``` `declare`/`defonce`/`defmulti`/`defrecord`/... is not supported in a book ``` -
  a book checks def, defn, data, law and proof forms only; rewrite the value
  as a plain def or defn.
- ``` `require`/`println`/... is not supported in a book ``` - unknown
  top-level forms are rejected, not skipped: a name used only there would
  escape the ordering rule. Only `ns`, `comment`, `def`, `defn`, `data`,
  `law` and `proof` belong at book top level.
- ``` `def` inside a body is not supported ``` - a book defines names at the
  top level only, in book order; hoist the definition.
- ``` duplicate case test constant ``` - a constant may match in only one
  clause (or one group); Clojure rejects duplicates at compile time, and a
  book is never compiled, so writ checks it.
- ``` `.` / `.foo` is host interop or effect code ``` - pure
  data-and-functions code only; rewrite without interop.
- ``` `set!` mutates a var ``` - writ checks pure code; an affine value cannot
  be mutated. Rewrite without mutation.
- ``` `recur` in `f` must be in tail position ``` - recur only compiles in
  tail position; move it to the tail or use a named self-call.
- ``` `recur` in `f` rebinds N value(s) but is passed M ``` - the frame
  contract, checked before quantities and the descend marking, so a
  wrong-arity recur is never masked by an affinity error.  recur rebinds
  exactly its frame: the loop's slots or the defn's parameters. Match the count.
- ``` `throw`/`new`/`.foo` is host interop or effect code ``` - writ checks
  pure data-and-functions code only; no host calls, no mutation, no effects.
- ``` duplicate parameter in `f` ``` - parameters are binders: rename one, or
  use `_` for a parameter you ignore (it may repeat).
- ``` def `x` must carry a value ``` - a book is never evaluated, so a def
  without a value would smuggle an unbound name into scope; write `(def x nil)`
  if you mean nil.
- ``` case test must be a compile-time constant ``` - quote the symbol
  (`(quote foo)`) to compare against it; bare symbols read like binders but
  are constants.
- ``` `Just`/`MaybeInt` is declared more than once ``` - a data type and its
  constructors are book-level names and may not collide with a def or defn.
- ``` `map` is used in `f` but is defined later ``` - the book defines its own
  `map`, so the core one no longer resolves: move the definition earlier or
  rename it.
- ``` `recur` in `f` cannot cross a `try` ``` - move the `loop` inside the
  `try`; recur compiles only inside the try's own loop.
- ``` a rest parameter must be followed by exactly one rest name ``` - `[x &]`,
  `[& a b]` and `[& &]` are malformed; write `[x & xs]`.
- ``` `f` takes 2 argument(s) but is passed 1 ``` - a book is never evaluated,
  so writ checks call arity itself; match the fn's (or constructor's) fixed
  arity, or its variadic minimum.
- ``` `f` takes at least 1 argument(s) but is passed 0 ``` - a variadic fn
  still requires its fixed parameters.
- ``` a keyword or set is called with no arguments ``` - the collection to
  read is missing; write `(:k m)` (a default is optional).
- ``` `a` and `b` are mutually recursive ``` - Bend's defs reference earlier
  names only, so no descent can be checked across a cycle of local fns;
  break the cycle or make each side self-recursive with descent.
- ``` a catch clause must be `(catch Class binder body*)` ``` - the catch
  clause needs a class symbol, a simple binder symbol and a body; a
  destructuring binder like `[x]` is not accepted.
- ``` the `finally` clause must be last in a `try` ``` - nothing may follow
  finally; catch clauses come before it.
- ``` only catch or finally clauses can follow a catch in a `try` ``` - a
  plain body form after a catch is not valid try syntax.
- ``` a `letfn` spec must be `(name [params] body*)` ``` - each spec needs a
  name, a params vector, and its body; ``` `letfn` requires a vector of fn
  specs ``` - the specs form itself must be a vector.
- ``` Wrong number of args to if, had: N ``` - `if` takes exactly a test,
  a then, and optionally an else; a fourth branch is not extra data.
- ``` Wrong number of args to var, had: N ``` / ``` The argument to `var`
  must be a symbol ``` - `var` takes exactly one symbol.
- ``` Bad binding form: `x` ``` - a binder (parameter, let/loop local,
  catch binder, letfn name) must be a simple symbol: no namespace, no
  dots.
- ``` First argument to def must be a symbol ``` / ``` Cannot def
  namespace qualified symbol ``` / ``` Too many arguments to def ``` - a
  def carries a name, an optional docstring, and one value.
- ``` requires a vector of parameters ``` - write `[x y]`, not `x` or
  `(x y)`; a list of arity vectors is the multi-arity error instead.
- ``` `g` takes 2 argument(s) but is passed 1 ``` / ``` takes at least 1
  argument(s) ``` - a call to a local fn (letfn, let-bound, anonymous)
  does not match its parameter vector; the same rule the book-fn arity
  gate enforces.
- ``` an anonymous fn takes 2 argument(s) but is passed 1 ``` - the fn
  literal in call position; give it its arguments.
- ``` `let` requires a vector for its bindings ``` / ``` `loop` requires
  a vector for its bindings ``` - write `(let [x 1] ...)`, not a bare
  form.
- ``` `case` requires at least one clause or a default ``` / ``` Wrong
  number of args to case, had: 0 ``` - a case with nothing to match can
  only ever throw.
- ``` First argument to defn must be a symbol ``` / ``` Cannot defn
  namespace qualified symbol ``` - a book is one namespace; defn names
  follow the same rules as def names.
- ``` a collection or symbol is called with no arguments ``` - a vector,
  map, set or quoted symbol is a lookup fn; give it the collection to
  read. ``` a lookup call ... takes at most the collection and a
  default ``` - two arguments is the maximum.
- ``` Unsupported special form: unquote ``` / ``` Unsupported special
  form: unquote-splicing ``` - an unquote that survives reading is always
  an error (syntax-quote consumes the legal ones at read time; the host
  throws the same message).
- ``` def `x` reads itself through a call in its own value ``` - the
  name is unbound during its own init, so using it as a call argument
  throws at load on the host.  Unforced storage (`(def v [1 v])`) is
  legal, and a self-reference inside a fn body is recursion.
- ``` a type parameter in `P` must be a simple symbol ``` - `(data P
  [a] ...)` binds type parameters; like any binder they are simple
  symbols, so [1 2], [foo/bar] and [a.b] are rejected.
- ``` a match arm must be `(pattern result)` ``` - each arm is exactly
  a pattern and its result; a bare symbol, a 1-element or 3-element arm
  is a shape error, as is a `match` with no arms at all.
- ``` Wrong number of args to quote, had: N ``` - quote takes exactly
  one form; jolt evaluates (quote a b) without complaint but the JVM
  compiler rejects it, so writ enforces the JVM contract.
- ``` cond requires an even number of forms ``` - cond (and cond-> /
  cond->>) takes test/expr pairs; a dangling test with no expr is a
  shape error.
- ``` `:-` in `f` must be followed by a return type ``` / ``` `:-` in `f`
  must be followed by a type ``` - a dangling annotation arrow; the type
  after `:-` is missing, so the annotation would silently vanish.
- ``` `1` in `f` is not a function ``` - numbers, strings, characters,
  booleans and nil can never be called.
- ``` `x` in `g` is not a function; a constant defined in this book
  cannot be called ``` - a def bound to a constant (a number, string,
  docstring-as-value, nil, collection, or a quoted fn form) is not
  callable at any arity. Wrap
  the fn in an actual fn value, or call something else.
- ``` `get` takes between 2 and 3 argument(s) but is passed 1 ``` /
  ``` `map` takes at least 1 argument(s) but is passed 0 ``` - the call
  does not match any arity of the clojure.core fn; the table comes from
  core's own :arglists, and a book def of the same name wins over it.
- ``does not descend: no argument is a structurally smaller part of its own
  parameter`` - recurse on a part destructured from that parameter, or on
  `dec`/`rest`/`next` of it. A computed value, the bare parameter, or a part
  of a DIFFERENT parameter does not count.
- ``shrinks `x` without a guard`` - test the column first: `(if (zero? x) ..)`
  on a Nat, `(pos? x)`, `(seq xs)`, `(empty? xs)`, or a truthiness test.
- ``refers to itself as a value`` - a self-reference must be a call head.
- ``argument N before the shrinking one must be passed unchanged`` - reorder
  the parameters so the accumulator rides after the shrinking one.
- ``is used more than once but is declared affine`` - add `^:many` to that
  binder. It may be a parameter, a local, or a pattern binder.
- ``is used once but is declared erased`` - drop `^:zero`, or stop using the
  binder.
- ``is used once but is declared erased`` on a `^:zero` local's init or an
  argument to a `^:zero` param - Clojure evaluates dead code, so those uses
  count (Bend erases them; writ cannot).
- ``shadows a parameter`` / ``duplicate binder`` - rename the local.
- ``the scrutinee of a `match` must be a parameter or a pattern binder`` -
  match a bound name, not the computed value.
- ``takes N type argument(s), got M`` - fix the type's arity.
- ``is reusable (^:many) but its type is not Data`` - drop `^:many`, or
  instantiate the type at Data arguments.
- ``is reusable (^:many) but has no type`` / ``no type writ can infer`` -
  annotate the binder with a Data type (`:- Nat`, `^Nat`).
- ``is captured by a fn passed to `map`, which may be called more than once``
  - mark the captured binder `^:many`, or pass it as an argument.
- ``destructured into overlapping binders`` - read each key once, or make the
  source `^:many`.
- ``expects T for argument N but is passed U`` / ``returns T but its body has
  type U`` / ``has type T, which is not a function`` - the annotation and the
  code disagree.
- ``law `x` is not filled: no proof discharges it`` - add the proof.
- ``discharges no law`` - the proof names a law that is not declared.
- ``re-proves law`` - delete the duplicate proof, a law is discharged once.
- ``cites law `x` before it is proved`` - move that proof after `x`'s own
  proof.
- ``duplicate law name`` - rename one of them.
- ``is defined later or is not a known name`` - move the def earlier, or
  qualify the name.

## Source map

- `writ.ann` metadata vocabulary, `writ.quant` the quantity lattice
- `writ.lower` the AST, `writ.uses` occurrence analysis
- `writ.check` quantities, termination, ordering
- `writ.kind` well-kindedness and the Data/Type lattice, `writ.demand` the
  erased-in-type rule
- `writ.match` match discipline, `writ.norm` conversion behind `refl`
- `writ.law` propositions, proofs and the gate, `writ.book` book orchestration
- `writ.defn` the surface macros, `writ.core` public entry points
