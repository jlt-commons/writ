# writ

writ checks plain Clojure against a contract that lives beside it. The code
never mentions writ. A separate spec namespace gives the public functions
their signatures and states laws about how they behave, and writ tells you
exactly where the code breaks them.

It is built for code an LLM writes. A person writes the spec: what the API
is and what must hold of it. The agent writes the implementation. writ is
the gate between them, and its report says what to fix: the rule that was
broken, or the law that failed, the smallest input that fails it, and the
value each side produced.

The static rules come from [Bend](https://github.com/HigherOrderCO/Bend):
pure code only, recursion that provably terminates, definitions in order,
types that fit. Behaviour is checked by running the laws, through
[test.check](https://github.com/clojure/test.check), against inputs
generated from the spec's types.

writ runs on [jolt](https://github.com/jolt-lang/jolt).

## The workflow

```
src/my/sort.clj           the implementation: plain Clojure, no writ
test/my/sort_spec.clj     the contract: spec, data, ann, law
test/my/sort_test.clj     runs the check
```

1. Write the spec. It names the namespace it constrains, signs the public
   fns and states the laws. This is the part a person owns.
2. The agent writes the implementation as ordinary Clojure.
3. Run the check. If it fails, hand the report back to the agent and repeat.
4. Keep the check in the test suite, so it gates every change.

writ is a test dependency. The spec and the check live on the test
classpath, so production code never loads writ.

```clojure
;; deps.edn
{:aliases
 {:test {:extra-paths ["test"]
         :extra-deps {io.github.jlt-commons/writ
                      {:git/url "https://github.com/jlt-commons/writ"
                       :git/sha "<sha>"}}}}}
```

## An example

The implementation:

```clojure
(ns my.sort)

(defn occurrences [x xs]
  (if (seq xs)
    (+ (if (= x (first xs)) 1 0) (occurrences x (rest xs)))
    0))

(defn insert [x xs]
  (if (seq xs)
    (if (<= x (first xs))
      (cons x xs)
      (cons (first xs) (insert x (rest xs))))
    (list x)))

(defn isort [xs]
  (if (seq xs)
    (insert (first xs) (isort (rest xs)))
    ()))
```

The spec:

```clojure
(ns my.sort-spec
  (:require [writ.spec :refer [spec ann law]]))

(spec my.sort)

(ann occurrences [Nat (List Nat) -> Nat])
(ann insert      [Nat (List Nat) -> (List Nat)])
(ann isort       [(List Nat) -> (List Nat)])

(defn ascending? [xs]
  (or (empty? xs) (apply <= xs)))

(law sorted      (forall [xs (List Nat)] (ascending? (isort xs))))
(law permutation (forall [x Nat, xs (List Nat)]
                   (= (occurrences x (isort xs)) (occurrences x xs))))
(law insert-empty (= (insert 3 ()) (list 3)))
```

The check:

```clojure
(ns my.sort-test
  (:require [clojure.test :refer [deftest is]]
            [writ.spec :as spec]))

(deftest sort-meets-its-spec
  (let [r (spec/check 'my.sort-spec)]
    (is (:ok r) (:message r))))
```

If `insert` dropped a value equal to the head, the report would read:

```
writ.spec: my.sort-spec against my.sort: FAILED

law `permutation` fails for
  x  = 9
  xs = [9 9]
  (occurrences x (isort xs)) => 1
  (occurrences x xs) => 2
  (shrunk from {x 9, xs [0 6 13 8 10 19 9 4 11 9 4 5 9 9 13 2 18]}, failing on test 20)
  (replay with {:seed 42})
```

A static failure stops the check before any law runs:

```
Writ: recursive call to `isort` does not descend: no argument is a
structurally smaller part of its own parameter (destructure it, or use
dec/rest/next of it under a test)
```

## Writing a spec

A spec namespace requires `writ.spec` and uses four forms.

- `(spec target.ns)` names the namespace it constrains. It comes first.
- `(ann f [A B -> R])` gives fn `f` its parameter and return types. Every
  public fn should have one; the report lists the ones that don't. A
  private helper that recurses over a collection needs one too, because
  writ has to know the collection is finite to accept the recursion.
- `(data Name Ctor (Ctor2 FieldType ...) ...)` declares a datatype the
  target's values use. `(data Box [a] (Wrap a))` takes type parameters.
- `(law name proposition)` states a law.

A spec may define its own helper fns, like `ascending?` above. They run
only when laws run.

### Types

Built in: `Nat Int Bool String Char Keyword Symbol Float Double Unit Any`,
`(List T)`, `(Vec T)`, `(Set T)`, `(Map K V)`, `(Tuple T ...)`, and
function types `(-> A B R)`. Declared types come from `data`.

`(List T)` means any seq: a list, a vector, a lazy seq or nil. Generated
inputs mix all four, so code that only works on one of them fails. `conj`,
for example, prepends to a list and appends to a vector.

### Data

A data value is a vector headed by its constructor keyword: `[:Leaf]`,
`[:Node l v r]`. The code builds one as a vector literal and takes it apart
with `case` on its tag:

```clojure
(defn size [t]
  (case (first t)
    :Leaf 0
    :Node (let [[_ l _ r] t] (+ 1 (size l) (size r)))))
```

writ checks this statically:

- The `case` names only constructors of the type, and covers every one
  unless it has a default.
- A clause destructures only the fields of its own constructor.
- A literal `[:Node ...]` has exactly the fields `Node` declares, and each
  field whose type is known fits. A type parameter takes its type from the
  first field that is exactly that parameter, and must agree after that.
- The value is read only through that `case`. `first`, `second` or `nth`
  anywhere else is rejected.

### Laws

A proposition is built from:

- `(= a b)`
- `(and P ...)`
- `(=> P Q)`, where cases in which `P` does not hold are skipped
- `(forall [x T, y U] P)`
- `(exists [x T] P)`
- any other expression, which holds when it is truthy

Inside a law, a free name refers first to the target's public fns, then to
the spec's own helpers, then to `clojure.core`.

## Running the check

`(writ.spec/check 'my.sort-spec)` returns a report map:

```clojure
{:ok          true
 :spec        my.sort-spec
 :target      my.sort
 :static      {:ok true}
 :laws        [{:law sorted :status :tested :trials 100 :seed 1732 :discarded 0} ...]
 :unspecified []                ; public fns with no ann
 :message     "writ.spec: my.sort-spec against my.sort: ok"}
```

It works in two stages.

1. **Static.** writ reads the target's source from the classpath, puts the
   `ann` types on its `defn`s and checks it (see below). If this fails,
   `:static` carries the error and no law runs.
2. **Laws.** Each law is discharged one of four ways, and `:status` says
   which:
   - `:proved`: `writ.norm` shows it holds for every input, without
     running anything. This covers identities such as `(+ n 0)` = `n`.
   - `:evaluated`: a law with no quantifiers, decided by running it once.
   - `:tested`: a `forall`, run by test.check on generated inputs. A
     failure is shrunk to a small counterexample.
   - `:witnessed`: an `exists`, found by test.check and shrunk to the
     simplest witness.

   A tested law has been tested, not proved; the status keeps the two
   apart. While laws run, the target's signed fns are instrumented, so a
   value of the wrong type fails at the fn that produced it.

Options: `:target` checks a different implementation against the same spec,
`:trials` is the number of test.check runs per law (default 100), `:seed`
replays a run (default random, reported per law), and `:max-size` is the
largest generated size (default 50).

`check!` does the same but throws with the message when anything fails.
`(spec/instrument 'my.sort-spec)` wraps the target's signed fns with runtime
argument and return checks for use at the REPL, and `unstrument` removes
them. `(spec/sample '(List Nat) {} 5)` shows what a type generates.

## What the static check enforces

These rules apply to the plain implementation.

- **Pure code.** No host interop (`throw`, `new`, `.foo`, `reify`), no
  effects (I/O, atoms and refs, futures, `eval`, var mutation,
  randomness), no reflection. Calls into other namespaces pass through
  unchecked.
- **Top-level forms.** Only `ns`, `comment`, `def` and `defn`. A
  `defmulti`, `defrecord`, `defmacro` or bare expression is rejected
  rather than skipped. Each fn has a single arity.
- **Order.** A definition refers only to definitions above it, so there is
  no mutual recursion. There are no forward declarations.
- **Termination.** Every recursive call, `recur` included, must pass a
  structurally smaller part of one parameter, under a test that proves the
  shrink:
  - `rest` and `next` need `seq` or `empty?`
  - `dec` needs `pos?`, or `zero?` on a `Nat`
  - element reads such as `first`, `nth` and destructured fields need the
    value to be non-nil. A truthiness test works, and so does a `case` on
    `(first t)`

  Parameters before the shrinking one pass through unchanged. `rest` only
  shrinks a collection writ knows is finite, which is one reason to sign
  the fn.
- **Arity and calls.** Every call matches its fn's arity, including
  `clojure.core` fns, and nothing that is not a fn is called.
- **Types.** Arguments fit the signed parameter types, and the body fits
  the signed return type. Unsigned code is inferred where writ can
  (literals, arithmetic, typed calls); an unknown type never fails on its
  own. A `Nat` widens to `Int`.
- **Data** is taken apart with `case` on its tag and built with the right
  fields, as described under [Data](#data).

## The annotated surface

writ can also check code that carries its annotations inline, through the
macros in `writ.defn`. This surface enforces Bend's full discipline,
including quantities, and states laws and proofs in the code. The books in
`examples/` still use it. They are being ported to spec namespaces.

```clojure
(require '[writ.defn :as w])

(w/data MaybeInt Nothing (Just Int))

(w/defn ^{:writ/descend true} add [^:many a :- Nat, b :- Nat] :- Nat
  (if (zero? a) b (add (dec a) b)))

(w/defn from-maybe [m :- MaybeInt]
  (w/match m :- MaybeInt
    (Nothing 0)
    ((Just x) x)))
```

On top of the rules above, this surface adds:

- **Quantities.** A binder with no mark is affine and used at most once.
  `^:many` makes it reusable, which requires a Data type (a function never
  is). `^:zero` makes it erased, so it must not be used.
- **Descent marker.** Recursion needs `^{:writ/descend true}`.
- **Type variables.** They are declared in the attr-map:
  `{:writ/forall [a, b :- Data]}`.
- **Data.** `w/data` values are `:Nothing` or `[:Just x]` and are taken
  apart only with `w/match`, which checks exhaustiveness. It also matches
  `Nat`, `Bool` and `(List T)`.
- **Laws and proofs.** `(w/law name prop)` must be discharged by a
  `(w/proof name law term)`. The terms are `refl`, `pair`, `(fn [x] ..)`
  and `(witness t pf)`, checked by `writ.norm`. It has no induction and
  does not unfold your own fns, so it can only prove identities; it cannot
  check behaviour. That is the gap `writ.spec` fills.

Every `w/` macro expands to the plain form it annotates, so annotated code
runs as if writ were absent. `writ.core/check-book` checks a quoted vector
of forms, and `writ.book/check-files` checks source files as one book.
`skills/writ/SKILL.md` lists every rule and error message.

## Modules

- `writ.spec`: spec namespaces, law checking, instrument
- `writ.book`: runs every rule over a namespace's forms
- `writ.check`: quantities, termination, ordering, effects, arity
- `writ.types`: type checking and tagged data
- `writ.kind`: type well-formedness and the Data/Type lattice
- `writ.lower`: macroexpanded forms to a small core AST
- `writ.uses`: path-sensitive occurrence analysis
- `writ.match`: `w/match` discipline
- `writ.norm`: normalisation and convertibility
- `writ.law`: propositions and the proof gate
- `writ.data`: data declarations
- `writ.quant`, `writ.ann`: the quantity lattice and its metadata
- `writ.defn`: the annotated surface macros
- `writ.core`: entry points for the annotated surface

writ.spec depends on `org.clojure/test.check`. The rest of writ has no
dependencies.

## Tests

```
jolt -M:test                   # or ./bin/test
cd examples && jolt -M:test    # every example book
```

`test/writ/spec_demo/` holds the worked example: an insertion sort and a
binary search tree, each with a spec, one correct implementation and
several broken ones. Every broken one is rejected with a report that points
at the fix.
