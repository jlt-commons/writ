# writ

writ checks plain Clojure against a spec of what the code is for. The spec
is the problem statement written so a machine can check it: signatures for
the public functions, and laws that say what their results mean. It lives
in its own namespace, and the code never mentions writ.

It is built for code an LLM writes. A person writes the spec, which is the
intent. The agent writes the implementation. writ is the gate between
them. Its report says what to fix: the rule that was broken, or the law
that failed, the smallest input that fails it, and the value each side
produced.

A spec is not a test suite. Tests pin down examples: this input gives that
output. A spec states what must hold for every input: the output is
ordered, and it has the same elements as the input. That is the meaning of
a sort, not a sample of it. writ also checks the spec itself. It rejects a
law that any implementation would satisfy, and it reports a function the
laws don't pin down, naming a trivial stand-in that would pass.

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
   fns and states what they mean. This is the part a person owns.
2. The agent writes the implementation as ordinary Clojure.
3. Run the check. If it fails, hand the report back to the agent and repeat.
4. Keep the check in the test suite, so it gates every change.

writ is a test dependency. The spec and the check live on the test
classpath, so production code never loads writ.

Note the quoting. `(spec my.sort)` is a macro inside the spec, so the
target namespace goes in unquoted. `(spec/check 'my.sort-spec)` is an
ordinary fn call, so the spec namespace it checks is quoted.

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

(ann insert      [Nat (List Nat) -> (List Nat)])
(ann isort       [(List Nat) -> (List Nat)])

(defn ascending? [xs]
  (or (empty? xs) (apply <= xs)))

(defn occurrences [x xs]
  (count (filter #(= x %) xs)))

;; a sort puts its input in order...
(law sorted (forall [xs (List Nat)] (ascending? (isort xs))))

;; ...and keeps every element, duplicates included
(law permutation (forall [x Nat, xs (List Nat)]
                   (= (occurrences x (isort xs)) (occurrences x xs))))

;; insert keeps an ordered list ordered, and adds exactly one x
(law insert-keeps-sorted (forall [x Nat, xs (List Nat)]
                           (=> (ascending? xs) (ascending? (insert x xs)))))
(law insert-adds (forall [x Nat, xs (List Nat)]
                   (= (occurrences x (insert x xs)) (inc (occurrences x xs)))))
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

## What a spec should say

Start from the problem, not the code. Ask what makes an answer right, and
write that down in the problem's own terms.

- **Characterise the result.** A sort's output is ordered and is a
  permutation of its input. Together those two laws are the whole meaning
  of sorting, and nothing else satisfies both.
- **Compare with a model.** When there is an obvious reference, say the
  code agrees with it: a search tree built from `xs` lists
  `(sort (distinct xs))`. The model can be slow or naive, because it only
  runs in the check.
- **Relate operations.** Say what the pieces do together: decoding an
  encoded value gives the value back, `insert` adds exactly one element,
  `pop` undoes `push`.
- **Keep invariants.** Say what every operation preserves: an ordered list
  stays ordered, a balanced tree stays balanced.
- **Use the spec's own vocabulary.** Measure results with helpers defined
  in the spec (`ascending?`, `occurrences`), never with the
  implementation's fns. A law that checks the code with the code is
  circular: if both are wrong in the same way, it still passes.

What a spec should not be:

- A list of examples. A law with no quantifier is fine as an anchor, but
  on its own it is only a test.
- A restatement of the types. `ann` already covers those.
- A restatement of the code, or a law that is true of anything. writ
  rejects these as vacuous.

writ enforces the last two points in the check:

- **Vacuous laws fail.** A law that calls no function of the target, or
  that `writ.norm` proves without looking at the implementation, holds for
  any code, so it says nothing about this code. Examples are
  `(= (isort xs) (isort xs))` and `(= (+ n 0) n)`.
- **Gaps fail.** Once every law holds, writ swaps each signed public
  function for well-typed stand-ins: a constant, an argument passed
  through, and the real result perturbed (reversed, missing its first
  element, one more, or another value of the return type). If some
  stand-in still satisfies every law, the spec does not pin that function
  down, and the report says which stand-in got through:

```
the spec does not pin down `isort`: every law still holds when it always returns ()
  or when it returns the real result without its first element
  State what `isort` must do, so that a law rejects this.
```

That report is what a spec with only the `sorted` law produces. Adding
`permutation` closes both gaps.

One more stand-in catches a spec made only of anchors. When every law
calls a function with the same argument fixed to literals, the laws say
what it does at those values and nothing else. The stand-in agrees with
the real function there and returns something different everywhere else.
For a classifier whose laws only mention the sentinels `-127`, `-2`, `-1`
and `0`, the report reads:

```
the spec does not pin down `classify-read`: every law still holds when it returns a different value whenever `n` is not one of -127, -2, -1, 0
  State what `classify-read` must do, so that a law rejects this.
```

The stand-ins are a fixed family, so a spec that rejects them all can still
be too weak. Passing this check is necessary for a good spec, not
sufficient.

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

A generated `Int` stays between `-max-size` and `max-size`, so -50 to 50
by default, and a `Nat` between 0 and `max-size`. A law quantified over
`Int` therefore never reaches a value like `-127`. When specific values
matter, such as a return code's sentinels, anchor each one with a law that
names it: `(law eof-sentinel (forall [e Bool] (= :eof (classify-read -127 e))))`.

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
 :gaps        []                ; fns the laws don't pin down
 :rejected    [{:fn isort ...}] ; per fn: its laws and the stand-ins they rejected
 :unspecified []                ; public fns with no ann
 :message     "writ.spec: my.sort-spec against my.sort: ok\n  `insert`: ..."}
```

It works in three stages, and each runs only if the one before passed.

1. **Static.** writ reads the target's source from the classpath, puts the
   `ann` types on its `defn`s and checks it (see below). If this fails,
   `:static` carries the error and no law runs.
2. **Laws.** Each law gets a `:status`:
   - `:vacuous`: it holds whatever the code does, so it fails; see
     [What a spec should say](#what-a-spec-should-say).
   - `:evaluated`: a law with no quantifiers, decided by running it once.
   - `:tested`: a `forall`, run by test.check on generated inputs. A
     failure is shrunk to a small counterexample.
   - `:witnessed`: an `exists`, found by test.check and shrunk to the
     simplest witness.

   A tested law has been tested, not proved; the status keeps the two
   apart. While laws run, the target's signed fns are instrumented, so a
   value of the wrong type fails at the fn that produced it.
3. **Adequacy.** When every law holds, each signed public fn is swapped for
   stand-ins, and any stand-in that satisfies every law is reported in
   `:gaps`. See [What a spec should say](#what-a-spec-should-say). A
   passing report lists, per fn, how many laws call it and how many
   stand-ins of each kind they rejected, so a fn that only a couple of
   constants were tried against stands out:

   ```
   writ.spec: my.sort-spec against my.sort: ok
     `insert`: 2 laws, 5 impostors rejected (2 constant, 1 pass-through, 2 perturbed)
     `isort`: 2 laws, 5 impostors rejected (2 constant, 1 pass-through, 2 perturbed)
   ```

Options: `:target` checks a different implementation against the same spec,
`:trials` is the number of test.check runs per law (default 100), `:seed`
replays a run (default random, reported per law), and `:max-size` is the
largest generated size (default 50). `:adequacy false` skips the third
stage, for example while a spec is still being written.

### Which fns qualify

Before writing a spec, `(spec/scan 'my.ns)` says which of a namespace's
top-level forms writ could check. It reads the source without loading it,
checks each form in order against the ones above it that passed, and gives
writ's own reason for each one that fails. A fn that fails only because it
recurses over a collection with no type is listed apart, since an `ann`
fixes that. A fn that calls a rejected one says which. For a namespace
that mixes pure code with IO:

```
writ.spec/scan writ.spec-demo.scan-mixed: 1 of 6 forms can be checked, 1 more once signed

can be checked:
  classify

can be checked once an `ann` types its collection:
  total: recursive call to `total` does not descend: argument 1 shrinks `xs` without a guard; ...

cannot be checked:
  shout (private): `.toUpperCase` is host interop or effect code; writ checks pure data-and-functions code only
  log!: `println` in `log!` is effect code (...); writ checks pure data-and-functions code only
  loud-classify: it uses `shout`, which writ cannot check
  Conn (defrecord): `defrecord` is not supported in a book; ...
```

The report map has the same in `:forms`, one entry per form with
`:status` `:ok`, `:needs-ann` or `:no` and a `:why`.

### Other entry points

`check!` does the same as `check` but throws with the message when anything fails.
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
