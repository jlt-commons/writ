---
name: writ
description: >-
  Use when writing a writ spec -- the problem statement as checkable laws
  about what code means (writ.spec: spec/ann/data/law) -- or the plain Clojure
  implementation it constrains, or when reading a writ.spec report or any
  "Writ:" error (purity, termination, ordering, arity, types, tagged data,
  failing, vacuous or gapped laws). Also for the annotated writ.defn surface
  (w/defn, ^:many, w/match, w/law, w/proof) used by the example books.
---

# writ

writ checks plain Clojure against a spec of what the code is for. A spec
namespace is the problem statement in checkable form: it signs the public
fns and states laws about what their results mean. The implementation never
mentions writ. `(writ.spec/check 'my.spec)` runs Bend's static rules over
the implementation's source using those types, runs the laws, and then
checks that the laws actually pin the code down. It returns a report that
names what is wrong. writ runs on jolt; writ.spec uses test.check.

## Who owns what

- The spec (`spec`, `ann`, `data`, `law`) is the contract. Usually a person
  writes it. Do not weaken a law, loosen an `ann`, or delete either to get a
  check to pass. If the spec looks wrong, say so and ask.
- The implementation is yours. Change it until `check` reports `:ok`.
- If you are asked to write the spec, write the intent: see
  [What a spec should say](#what-a-spec-should-say).
- A report that fails is the next thing to fix. Read the whole message: it
  names the rule or law, the input, and the values.

## A spec

```clojure
(ns my.sort-spec
  (:require [writ.spec :refer [spec data ann law]]))

(spec my.sort)                                   ; the namespace it constrains

(ann insert [Nat (List Nat) -> (List Nat)])      ; one per public fn
(ann isort  [(List Nat) -> (List Nat)])

(defn ascending? [xs] (or (empty? xs) (apply <= xs)))   ; the spec's own
(defn occurrences [x xs] (count (filter #(= x %) xs)))  ; vocabulary

(law sorted      (forall [xs (List Nat)] (ascending? (isort xs))))
(law permutation (forall [x Nat, xs (List Nat)]
                   (= (occurrences x (isort xs)) (occurrences x xs))))
(law insert-keeps-sorted (forall [x Nat, xs (List Nat)]
                           (=> (ascending? xs) (ascending? (insert x xs)))))
(law insert-adds (forall [x Nat, xs (List Nat)]
                   (= (occurrences x (insert x xs)) (inc (occurrences x xs)))))
```

- `(spec ns)` comes first.
- `(ann f [A B -> R])`: the parameter count must match the fn, which has a
  single arity. A private helper that recurses over a collection needs an
  `ann` too, or writ cannot tell the collection is finite.
- `(data Tree Leaf (Node Tree Nat Tree))`, or `(data Box [a] (Wrap a))`
  with type parameters.
- Types: `Nat Int Bool String Char Keyword Symbol Float Double Unit Any`,
  `(List T) (Vec T) (Set T) (Map K V) (Tuple T ...)`, `(-> A R)`, and
  declared data. `(List T)` is any seq: list, vector, lazy seq or nil.
- A law is built from:
  - `(= a b)`
  - `(and P ...)`
  - `(=> P Q)`; a case where `P` does not hold is skipped
  - `(forall [x T, y U] P)`
  - `(exists [x T] P)`
  - any expression, which holds when it is truthy

  A free name refers first to the target's public fns, then to the spec's
  helpers, then to clojure.core. Laws cannot quantify over fn types,
  because no generator exists for them.

## What a spec should say

A spec says what makes an answer right, in the problem's terms, for every
input. It is not a set of examples (that is a test) and not a description
of the algorithm (that is the code).

- **Characterise the result.** For a sort: the output is ordered and is a
  permutation of the input. Nothing else satisfies both.
- **Compare with a model.** Where a simple reference exists, say the code
  agrees with it: `(= (to-list (build xs)) (sort (distinct xs)))`. The
  model may be slow; it only runs in the check.
- **Relate operations.** Round trips (`decode` after `encode`), inverses
  (`pop` after `push`), and exact effects (`insert` adds one `x`).
- **Keep invariants.** Say what every operation preserves.
- **Measure with the spec's own helpers.** Never use the implementation's
  fns to judge its results. A law that checks the code with the code is
  circular.

writ rejects a spec that does not do this:

- A law is `:vacuous`, and fails, when it calls no fn of the target or
  when writ.norm proves it without the code. `(= (isort xs) (isort xs))`
  and `(= (+ n 0) n)` are vacuous. Rewrite it to say what the code does.
- A **gap** is reported when every law holds but a trivial stand-in for a
  signed public fn would also satisfy them all. The stand-ins are a
  constant, an argument passed through, and the real result reversed,
  missing its first element, or plus one. The fix is a law that the
  stand-in breaks, and that states intent: add `permutation` so that
  "always returns ()" fails. Never special-case the stand-in in the code.

Rejecting every stand-in is necessary, not sufficient. Still ask whether
the laws say everything the problem statement says.

## The implementation

Plain Clojure, with no writ require and no annotations. writ rejects:

- Effects and interop: I/O, atoms and refs, futures, `eval`, `throw`,
  `new`, `.method`, `reify`, reflection.
- Top-level forms other than `ns`, `comment`, `def` and `defn`: no
  `defmulti`, `defrecord`, `defmacro`, `declare` or bare expressions.
  Each fn has one arity.
- A reference to a definition further down. There is no mutual recursion,
  so put helpers first.
- Recursion that does not provably descend. Each recursive call or `recur`
  must pass a strict part of one parameter, under a test on it:
  - `(rest xs)` or `(next xs)` under `(seq xs)` or `(empty? xs)`, and only
    on a collection typed finite, which the `ann` provides
  - `(dec n)` under `(pos? n)`, or `(zero? n)` on a `Nat`
  - fields from destructuring or `first`/`nth` under a non-nil test,
    including a `case` on `(first t)`

  Parameters before the shrinking one pass through unchanged, so
  accumulators go after it.
- Calls with the wrong arity, and calls to non-fns.
- Arguments that do not fit a callee's `ann`, or a body that does not fit
  the fn's own return type.

### Data values

A spec data value is a vector headed by its constructor keyword. Build it
as a literal and take it apart with `case` on the tag:

```clojure
(defn insert [x t]
  (case (first t)
    :Leaf [:Node [:Leaf] x [:Leaf]]
    :Node (let [[_ l v r] t]
            (cond (< x v) [:Node (insert x l) v r]
                  (> x v) [:Node l v (insert x r)]
                  :else t))))
```

The `case` must list every constructor, or carry a default, and name no
others. A clause destructures only its constructor's fields. A literal
`[:Node ...]` carries exactly the declared fields, of fitting types. Read
the tag with `case (first t)` only: `first`, `second` or `nth` of a data
value anywhere else is rejected.

## Running the check

```clojure
(require '[writ.spec :as spec])
(spec/check 'my.sort-spec)                        ; report map
(spec/check 'my.sort-spec {:seed 42})             ; replay a failure
(spec/check 'my.sort-spec {:target 'my.sort2})    ; same spec, other impl
(spec/check! 'my.sort-spec)                       ; throws with the message
(spec/sample '(List Nat) {} 5)                    ; what a type generates
(spec/instrument 'my.sort-spec)                   ; runtime arg/return checks
```

In a test: `(let [r (spec/check 'my.sort-spec)] (is (:ok r) (:message r)))`.
Other options are `:trials`, the test.check runs per law (default 100),
`:max-size`, the largest generated size (default 50), and
`:adequacy false`, which skips the gap check while a spec is being drafted.

## Reading a report

`:static` fails first. A static failure is a single `Writ:` message, and no
law runs until it is fixed. After that, each law has a `:status`:

- `:vacuous`: true of any implementation; the spec must change.
- `:evaluated`: a law with no quantifiers, run once.
- `:tested`: passed test.check's trials. This is evidence, not proof.
- `:witnessed`: an `exists` law, and a value was found.
- `:failed`: see the message.

```
law `permutation` fails for
  x  = 9
  xs = [9 9]
  (occurrences x (isort xs)) => 1
  (occurrences x xs) => 2
  (shrunk from {x 9, xs [0 6 13 ...]}, failing on test 20)
  (replay with {:seed 42})
```

The counterexample is already shrunk. Work out why the implementation
gives the left-hand value for that input: here, a duplicate is dropped.
Each line under a predicate law shows what one argument evaluated to. A
vector in `xs` means the input was a vector: the code must accept any seq.
While laws run, the target's fns are instrumented, so a line like
`` `insert` returns (List Nat), but returned ... `` points at the fn that
produced a badly typed value. After a fix, rerun with the same `:seed` to
confirm it, then without one.

## Fixing rejections

### Spec and law failures

- ``law `x` is vacuous: it calls no fn of ns`` / ``writ.norm proves it
  without looking at the implementation`` - the law is true of any code.
  Restate it as a claim about what the target's fns return.
- ``the spec does not pin down `f`: every law still holds when it ...`` -
  the named stand-in satisfies the spec. Add a law about `f`'s meaning
  that the stand-in breaks. If you own only the implementation, report the
  gap to the spec's owner; the code is not at fault.
- ``law `x` fails for ...`` - the implementation is wrong for that input;
  see [Reading a report](#reading-a-report).
- ``the hypothesis never held in N trials`` - no generated input satisfied
  the `=>` premise, so the law tested nothing. Tell the spec's owner.
- ``no witness among N generated values`` - the `exists` law found no
  value. Either the implementation is wrong, or the witness is too rare to
  generate.
- ``cannot generate values of type `T` `` - the law quantifies over a
  function type or an undeclared name.
- ``the spec gives `f` a signature, but `ns` defines no fn `f` `` - define
  `f`, or check its spelling. The spec names the API.
- ``` `ann f` gives N parameter type(s) but `f` takes M ``` - match the
  signature. The spec is the contract.
- ``` `f` is multi-arity; `ann` gives a single signature ``` - write one
  arity.
- ``` `f` argument N (x) expects T, got v ``` / ``` `f` returns T, but
  returned v ``` - an instrumented call saw a value outside the signature.
- ``cannot find the source of `ns` on the classpath`` - the target file is
  not under a source path.
- ``is not a spec namespace`` - the namespace has no `(spec target)` form.

### Tagged data

- ``the `case` on `t` (Tree) does not handle :Leaf`` - add the clause, or a
  default.
- ``:Nod is not a constructor of Tree (Leaf, Node)`` - fix the keyword.
- ``Node takes 3 field(s) but is built with 2`` - build `[:Node l v r]`.
- ``field N of Node expects T but is given U`` - that field has the wrong
  value. Check the field order in the `data` declaration.
- ``field N of C expects a, which field M made T, but is given U`` - a type
  parameter was given two different types.
- ``Node has 3 field(s), but `t` is read at position 4`` - destructure at
  most the tag plus the fields.
- ``has data type Tree; take it apart with `(case (first t) ...)` `` - read
  a data value only through a `case` on its tag.

### Structural rules (plain and annotated code)

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
- ``` `set!` mutates a var ``` - writ checks pure code. Rewrite without
  mutation.
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
- ``` Wrong number of args to quote, had: N ``` - quote takes exactly
  one form; jolt evaluates (quote a b) without complaint but the JVM
  compiler rejects it, so writ enforces the JVM contract.
- ``` cond requires an even number of forms ``` - cond (and cond-> /
  cond->>) takes test/expr pairs; a dangling test with no expr is a
  shape error.
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
  ``must be a finite collection`` means `x` has no finite type: sign the fn
  with `ann` in the spec.
- ``refers to itself as a value`` - a self-reference must be a call head.
- ``argument N before the shrinking one must be passed unchanged`` - reorder
  the parameters so the accumulator rides after the shrinking one.
- ``takes N type argument(s), got M`` - fix the type's arity.
- ``expects T for argument N but is passed U`` / ``returns T but its body has
  type U`` / ``has type T, which is not a function`` - the code disagrees
  with the types in its `ann` (or annotation). Fix the code, not the `ann`.
- ``is defined later or is not a known name`` - move the def earlier, or
  qualify the name.
### Annotated surface only (writ.defn)

These come from `w/defn`, `w/match`, `w/law` and `w/proof`, which the
example books use.

- `` `f` is recursive: mark it ^{:writ/descend true} `` - add the attr map, or
  rewrite without recursion.
- ``` a match arm must be `(pattern result)` ``` - each arm is exactly
  a pattern and its result; a bare symbol, a 1-element or 3-element arm
  is a shape error, as is a `match` with no arms at all.
- ``` `:-` in `f` must be followed by a return type ``` / ``` `:-` in `f`
  must be followed by a type ``` - a dangling annotation arrow; the type
  after `:-` is missing, so the annotation would silently vanish.
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
- ``is reusable (^:many) but its type is not Data`` - drop `^:many`, or
  instantiate the type at Data arguments.
- ``is reusable (^:many) but has no type`` / ``no type writ can infer`` -
  annotate the binder with a Data type (`:- Nat`, `^Nat`).
- ``is captured by a fn passed to `map`, which may be called more than once``
  - mark the captured binder `^:many`, or pass it as an argument.
- ``destructured into overlapping binders`` - read each key once, or make the
  source `^:many`.
- ``law `x` is not filled: no proof discharges it`` - add the proof.
- ``discharges no law`` - the proof names a law that is not declared.
- ``re-proves law`` - delete the duplicate proof, a law is discharged once.
- ``cites law `x` before it is proved`` - move that proof after `x`'s own
  proof.
- ``duplicate law name`` - rename one of them.

## The annotated surface

`writ.defn` puts the annotations in the code and adds Bend's full
discipline on top of the rules above. The books in `examples/` are
written this way, as `main.clj`, `LAWS.clj` and `PROOF.clj` checked
together by `writ.book/check-files`. They are being ported to spec
namespaces.

- `(w/defn f [a :- Nat, ^:many b :- Nat] :- Nat body)`: `:-` gives types.
  An unmarked binder is affine: used at most once, with zero allowed.
  `^:many` makes it reusable, which requires a Data type. `^:zero` makes it
  erased, never used. Quantities cover every binder, locals and pattern
  binders included. Branches join, and sequential uses add.
- Recursion needs `^{:writ/descend true}` on the defn.
- Type variables go in the attr-map: `{:writ/forall [a, b :- Data]}`.
- `w/data` values are `:Nil` or `[:Cons h t]`, and only `w/match` takes
  them apart. It is exhaustive; a trailing lowercase arm catches the rest.
  The scrutinee must be a parameter or pattern binder. It also matches
  `Nat`, `Bool` and `(List T)`.
- Every `(w/law name prop)` needs exactly one `(w/proof name law term)`.
  The terms are `refl`, `(pair ..)`, `(fn [x] ..)` and `(witness t pf)`.
  `refl` needs both sides convertible under writ.norm, which has no
  induction and does not unfold your own fns. It can only prove identities;
  checking behaviour is what writ.spec is for.

## In this repo

```sh
rm -rf ~/.jolt/aot-cache .jolt   # the AOT cache can serve stale namespaces
jolt -M:test                      # engine suite
cd examples && jolt -M:test       # every example book
```

When a test run disagrees with a direct `jolt -e` of the same code, clear the
AOT cache before debugging. That is a known jolt issue, not a writ bug.

`test/writ/spec_demo/` holds worked specs, a sort and a tree, each with
broken implementations and the reports they produce.

## Source map

- `writ.spec` spec namespaces, law checking with test.check, instrument
- `writ.book` runs every rule over a namespace's forms
- `writ.check` quantities, termination, ordering, effects, arity
- `writ.types` types and tagged data, `writ.kind` well-kindedness
- `writ.lower` the AST, `writ.uses` occurrence analysis
- `writ.match` `w/match`, `writ.norm` conversion behind `refl`,
  `writ.law` propositions and the proof gate
- `writ.defn` the annotated macros, `writ.core` its entry points
