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

A spec namespace requires `writ.spec` and uses six forms.

- `(spec target.ns)` names the namespace it constrains. It comes first.
- `(ann f [A B -> R])` gives fn `f` its parameter and return types. Every
  public fn should have one; the report lists the ones that don't. A
  private helper that recurses over a collection needs one too, because
  writ has to know the collection is finite to accept the recursion.
- `(data Name Ctor (Ctor2 FieldType ...) ...)` declares a datatype the
  target's values use. `(data Box [a] (Wrap a))` takes type parameters.
- `(law name proposition)` states a law.
- `(calls f [g ...])` states exactly which fns `f` calls. See
  [The call graph](#the-call-graph).
- `(machine name {...})` states that a fn steps a state machine by a
  transition table. See [Machines](#machines).

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
  unless it has a default. That holds for a value destructured from a
  typed `Tuple` too: with a game typed `(Tuple Phase Ball)`,
  `(let [[phase ball] game] (case (first phase) ...))` must cover every
  `Phase`.
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

### The call graph

Laws say what the code computes. They can't say how the code is put
together, and an implementation can compute the right thing through the
wrong structure: it inlines a helper instead of calling it, so the two
drift apart the next time the helper changes, or it skips a layer and
checks validity itself instead of going through the fn that owns the
rule. Every law still holds. `calls` states the structure:

```clojure
(ns my.pipeline-spec
  (:require [clojure.string :as str]
            [writ.spec :refer [spec ann law calls]]))

(spec my.pipeline)

(calls normalize [str/lower-case str/trim])
(calls respond   [valid?])
(calls handle    [normalize respond])   ; not valid?: respond owns that
```

`(calls f [g ...])` means `f`'s direct calls are exactly that set, no
more and no fewer. The call graph is read from `f`'s source:

- A simple name is one of the target's own fns. A qualified name is a fn
  of another namespace, resolved through the spec's aliases, so
  `str/trim` is `clojure.string/trim`.
- A fn counts when it is called or referred to as a value, as in
  `(map normalize xs)`.
- `clojure.core`, host members and `f` calling itself are left out.
  Recursion is the termination rule's business.
- A local binding that shadows a fn is not a call to it. The body is
  lowered and its locals renamed apart before the graph is read.

A `calls` failure is reported beside the laws, and it fails the check:

```
the call graph of `handle` is not the one the spec gives
  `handle` does not call `respond`, which the spec says it calls
  `handle` calls `valid?`, which the spec does not list
  the spec says `handle` calls exactly normalize, respond. Call through the layers the spec names instead of around them.
```

A passing report lists each fn's call set.

`calls` also guards the line between pure code and effects. The static
check lets calls into other namespaces through unchecked, so a pure core
that writes to a storage namespace passes it, and passes every law that
doesn't look at the store. Its call set names the stray call:
`` `shorten` calls `shortener.store/remember!`, which the spec does not
list``. [examples/](examples/README.md#shortener) has this case, run
against a real server.

`(spec/call-graph 'my.ns)` returns the graph of any namespace as
`{f #{g ...}}`. It reads the source without loading or checking it, so it
works on effect code too, and it's the quickest way to write a first
`calls` form. `(spec/mermaid 'my.ns)` renders the same graph as a mermaid
flowchart. Given a spec namespace, `(spec/mermaid 'my.spec)` draws the
target's graph with the spec laid over it. A call the spec doesn't list
is a dotted edge marked `not in spec`, and a listed call the code doesn't
make is an edge marked `missing`:

```
flowchart LR
  handle["handle"]
  normalize["normalize"]
  respond["respond"]
  valid_Q["valid?"]
  handle --> normalize
  handle -.->|not in spec| valid_Q
  respond --> valid_Q
  handle --x|missing| respond
```

writ also uses the call graph in its static rules, whether or not the
spec has `calls` forms:

- A definition refers only to definitions above it, so the graph has no
  cycles except self-recursion. A defn and the local fns it binds can't
  be mutually recursive either.
- `scan` walks the graph: a fn that calls one writ can't check is reported
  with "it uses `f`, which writ cannot check", so one effect deep in a
  call chain shows up at every caller above it.

### Machines

Some code is a state machine: a screen flow, a protocol, an order's
lifecycle. Its meaning is a transition table, and a table can be checked
exhaustively instead of sampled:

```clojure
(data Screen Logo Title Options Gameplay Paused Ending)
(data Event Timeout Confirm Configure Back Pause Finish Quit)

(ann next-screen [Screen Event -> Screen])

(machine screens
  {:step next-screen
   :start [:Logo]
   :transitions {[:Logo]     {[:Timeout] [:Title]}
                 [:Title]    {[:Confirm] [:Gameplay], [:Configure] [:Options]}
                 [:Options]  {[:Back] [:Title]}
                 [:Gameplay] {[:Pause] [:Paused], [:Finish] [:Ending]}
                 [:Paused]   {[:Pause] [:Gameplay], [:Back] [:Gameplay], [:Quit] [:Title]}
                 [:Ending]   {[:Confirm] [:Title]}}
   :final  [[:Title]]
   :never  [[[:Title] [:Logo]]]
   :before [[[:Gameplay] [:Ending]] [[:Title] [:Gameplay]]]})
```

writ checks two things. First, the code against the table: `:step` is run
on every state and every event, and each answer must be the table's, or
the same state where the table lists nothing. The states and events come
from the step fn's `ann` when their types are data whose constructors
have no fields; otherwise `:states` and `:events` list them. Here that is
42 pairs, all of them:

```
machine `screens`: `next-screen` does not follow its table
  (next-screen [:Title] [:Pause]) is [:Paused], but the table says [:Title] (no transition listed: the state stays)
```

Second, the table against its own rules:

- every state is reachable from `:start`
- `:final`: from every reachable state, some final state can be reached,
  so nothing is a trap
- `:never [a b]`: no path leads from `a` to `b`
- `:before [a b]`: every path from `:start` to `b` passes through `a`

A broken rule is reported with the path that breaks it:

```
machine `screens`: the table breaks its own constraints
  from [:Options] no final state can be reached
  [:Title] must never lead to [:Logo], but it does: [:Title] -[:Confirm]-> [:Gameplay] -[:Pause]-> [:Paused] -[:Quit]-> [:Logo]
```

The table also takes part in the adequacy check as a law would, so a
machine alone pins its step fn down. `(spec/mermaid 'my.spec {:machine
'screens})` draws the table as a mermaid `stateDiagram-v2`.

## Running the check

`(writ.spec/check 'my.sort-spec)` returns a report map:

```clojure
{:ok          true
 :spec        my.sort-spec
 :target      my.sort
 :static      {:ok true}
 :laws        [{:law sorted :status :proved :evidence :proof ...}
               {:law smallest-first :status :tested :evidence :test :trials 100 ...} ...]
 :proof       {:require :tested :proved 6 :tested 1 :laws 7}
 :gaps        []                ; fns the laws don't pin down
 :rejected    [{:fn isort ...}] ; per fn: its laws and the stand-ins they rejected
 :calls       [{:fn handle :calls [normalize respond] :status :ok} ...]
 :machines    [{:machine screens :status :ok :states 6 :events 7} ...]
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
   - `:proved`: a law that passed its tests and that the prover also
     derived from the code's source for every input; see
     [Proofs](#proofs). `:proof` says how, for example "by induction on
     xs, splitting on (<= x xs-h)".

   A tested law has been tested, not proved; the status keeps the two
   apart. A tested law the prover could not prove carries `:unproved`
   with the reason. Each law's `:evidence` is `:proof` (proved,
   evaluated or witnessed) or `:test`, and `:proof` in the report counts
   them. When the spec requires proof, a law that is only tested gets
   `:status :unproved` and fails; see [Requiring proof](#requiring-proof). While laws run, the target's signed fns are instrumented, so a
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

The `calls` forms are checked once the static stage passes, beside the
laws, and each gets an entry in `:calls` with `:status` `:ok` or
`:failed`, plus `:missing` and `:extra` when it failed. Each `machine`
gets an entry in `:machines`; a failed one carries `:mismatches`, one
`{:state :event :expected :actual}` per pair the code gets wrong, and
`:errors` for the table's own rules.

Options: `:target` checks a different implementation against the same spec,
`:trials` is the number of test.check runs per law (default 100), `:seed`
replays a run (default random, reported per law), and `:max-size` is the
largest generated size (default 50). `:adequacy false` skips the third
stage, for example while a spec is still being written, and
`:prove false` skips the prover. `:require` sets the evidence every law
needs, in place of the spec's own.

### Requiring proof

A tested law has passed some trials; a proved one holds for every input.
By default a spec accepts either, and the report says which each law got:

```
writ.spec: my.sort-spec against my.sort: ok
  6 of 7 laws proved; tested, not proved: smallest-first
```

A spec can require proof. Then a law that is only tested fails:

```clojure
(spec my.sort {:require :proved})
```

```
law `smallest-first` is tested, not proved, and the spec requires proof
  the prover: no proof found
  ...
```

A single law can ask for more or less than the spec. Letting a law off
proof takes a reason, and every report shows it, so an unproved law can't
go unnoticed:

```clojure
(law sorted {:require :proved} ...)                      ; in a spec that allows tests
(law smallest-first
  {:require :tested :because "the prover has no model of min over a list yet"}
  (forall [xs (List Nat)] ...))
```

A closed law that evaluates to true, and an `exists` law with a witness,
count as proved: running pure, terminating code on fixed inputs decides
them.

### Proofs

After a `forall` law passes its tests, writ tries to prove it from the
code. It translates the law and the target's `defn`s into terms and
rewrites them to normal form. When that isn't enough, it tries structural
induction on each quantified variable, with the law at every smaller value
as a hypothesis:

- a list is nil, empty, or a head and a tail
- a `Nat` is 0 or p + 1
- a datatype has one case per constructor

Within a case, the prover:

- splits an open integer comparison into its two outcomes, and
  substitutes an equality that holds
- splits an unknown tail into empty, and a head and a tail. That is how
  `insert-keeps-sorted` sees the second element.
- decides integer conditions from all the facts at once (Fourier-Motzkin
  elimination, tightened for integers), so `a <= b`, `b <= c` and
  `c < a` are seen to contradict each other

When a case still isn't closed, the prover tries two things:

- **Generalising.** It uses an equality hypothesis the other way round,
  replaces the recursive call that brings in with a fresh variable, and
  proves that more general goal by an induction of its own.
  `permutation` is proved this way, with `(isort xs-t)` generalised.
- **An accumulator.** A fold that grows an accumulator by addition from
  0, as a `loop` or a `reduce`, is first proved to give acc plus the fold
  from 0, from any integer acc, by induction with acc left free in the
  hypothesis. The law is then proved citing that.

A law proved earlier is a lemma for the laws after it: an equality
rewrites its left side to its right, anything else rewrites to true, when
its hypotheses hold. The passes repeat until nothing new is proved, so a
law may cite one that comes later in the spec. A law that is only tested
is never cited. The report names what each proof used:

```
writ.spec: my.sort-spec against my.sort: ok
  law `sorted` proved by induction on xs, citing insert-keeps-sorted
  law `permutation` proved by induction on xs, generalising (isort xs-t)
  law `insert-keeps-sorted` proved by induction on xs, splitting on (<= x xs-h), with cases on xs-t
  law `insert-adds` proved by induction on xs
```

The model follows Typed Clojure's, so the prover keeps the distinctions
Clojure makes:

- `nil` and `()` are different values, and `seq` is the bridge between
  them. `rest` is never nil, and `next` can be.
- Lists, vectors, cons cells and lazy seqs are one kind of value. The ops
  that tell them apart (`conj`, `peek`, `vector?`, ...) are outside the
  model, so a law that needs them stays tested.
- A lazy seq is truthy before it is realised, so deciding one never runs
  its elements.
- `=` is Clojure's: sequentials compare element by element, `1` never
  equals `1.0`, and a term equals itself only when no float can be inside,
  because `NaN` is not `=` to itself.
- Integers are exact (jolt promotes on overflow). `+` is associative and
  commutative only on integers. Floats get no algebra. A term counts as
  an integer only when its form or a proved fact says so, never because a
  signature says so.

A proof holds for every input on which the law's terms return a value.
That is Typed Clojure's notion of soundness, well-typed code returns or
throws. Since writ also runs every law, an input where a term throws still
fails the check. One step takes a signature at its word: a generalised
call ranges over its fn's signed return type. The laws' runs check every
signature on every trial.

Several things guard the prover itself:

- **The checker.** Every proof is replayed before it is reported, by a
  checker that searches for nothing. It rebuilds each step and confirms
  it: an induction's cases are exactly its type's cases, each split
  proves both sides, a generalisation uses a hypothesis the case really
  has, and a lemma is cited only if it was proved. A proof it rejects is
  not reported. What must be trusted is the rewrite rules, the induction
  schemes and the checker, not the search.
- Each rewrite rule is checked against the runtime by test.check.
- Random closed terms are normalised and run, to check that the
  normaliser agrees with jolt.
- A proof must unfold one of the target's own definitions. One that never
  looks at the code would say nothing about it.
- A law that is proved and then refuted by a test value is reported as a
  writ bug.

The prover covers:

- `seq`, `first`, `rest`, `next`, `second`, `empty?`, `count`, `cons`,
  `list`, `vector`, `concat`, `filter`, `map`, `reduce` and `nth`
- `=`, integer arithmetic and comparisons, `integer?`, `if`, `case`, `let`
  and destructuring
- core fns passed as values, with `apply` of `<=`, `<`, `>=`, `>` and `+`,
  so a predicate like `(apply <= xs)` translates
- fn literals, `loop`/`recur`, and the target's and the spec's own
  `defn`s

Anything else leaves the law tested, with `:unproved` saying why, for
example "outside the prover: the name `min`".

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
  Conn (defrecord): `defrecord` is not supported: in the code a spec covers, writ checks def and defn forms only (...)
```

The report map has the same in `:forms`, one entry per form with
`:status` `:ok`, `:needs-ann` or `:no` and a `:why`.

### Other entry points

`check!` does the same as `check` but throws with the message when anything fails.
`(spec/instrument 'my.sort-spec)` wraps the target's signed fns with runtime
argument and return checks for use at the REPL, and `unstrument` removes
them. `(spec/sample '(List Nat) {} 5)` shows what a type generates.
`(spec/call-graph 'my.ns)` and `(spec/mermaid 'my.ns)` read a namespace's
call graph; see [The call graph](#the-call-graph).

## What the static check enforces

These rules apply to the plain implementation.

- **Pure code.** No host interop (`throw`, `new`, `.foo`, `reify`, static
  members such as `System/getenv` or `Math/abs`), no effects (I/O, atoms
  and refs, futures, `eval`, var mutation, randomness), no reflection.
  Calls into other namespaces pass through unchecked. writ reads source
  without loading it, so a qualified name whose qualifier ends in a
  capitalised segment is taken to be a class.
- **Top-level forms.** Only `ns`, `comment`, `def` and `defn`. A
  `defmulti`, `defrecord`, `defmacro` or bare expression is rejected
  rather than skipped. Each fn has a single arity.
- **Order.** A definition refers only to definitions above it, so there is
  no mutual recursion. There are no forward declarations.
- **Termination.** Every recursive call, `recur` included, must pass a
  structurally smaller part of one parameter, under a test that proves the
  shrink:
  - `rest` and `next` need `seq` or `empty?`
  - `dec` needs `pos?`, or `zero?` on a `Nat`. A chain of them needs a
    guard at each depth: `(dec (dec n))` under `(zero? n)` and
    `(zero? (dec n))` both false
  - `(- n k)` for a literal `k` is `k` decs, so it needs `n` to be at
    least `k`; `(< n k)` false or `(>= n k)` true proves it, and so does
    any comparison of `n` with a literal that implies it
  - element reads such as `first`, `nth` and destructured fields need the
    value to be non-nil. A truthiness test works, and so does a `case` on
    `(first t)`

  A test may sit inside `and`: `(if (and (pos? fuel) (pos? n)) ...)`
  proves both in its then branch. An `or` proves each of its tests false
  in its else branch. A recursion with no structural measure, such as one
  on `(quot n 62)`, takes a fuel parameter that counts down, as
  `encode-id` in [examples/shortener](examples/src/shortener/core.clj)
  does.

  Parameters before the shrinking one pass through unchanged, so an
  accumulator goes after the collection it walks, in the parameters or
  the `loop` bindings. `rest` only shrinks a collection writ knows is
  finite, which is one reason to sign the fn. The loops that `doseq` and
  similar macros expand to are checked the same way, and the error names
  the collection they walk.
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
including quantities, and states laws and proofs in the code.

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

- `writ.spec`: spec namespaces, law checking, the call graph, instrument
- `writ.prove`: the proof search; `writ.prove.term`, `writ.prove.rewrite`
  and `writ.prove.translate` hold the terms, the rewrite rules and the
  translation from Clojure; `writ.prove.scheme` the steps a proof is made
  of, and `writ.prove.check` the checker that replays every proof
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

writ.spec depends on `org.clojure/test.check`, and writ.prove on
`org.clojure/core.logic`, whose unification matches the rewrite rules. The
rest of writ has no dependencies.

## Tests

```
jolt -M:test                   # or ./bin/test
cd examples && jolt -M:test    # the example programs and their specs
```

`test/writ/spec_demo/` holds the worked example: an insertion sort and a
binary search tree, each with a spec, one correct implementation and
several broken ones. Every broken one is rejected with a report that points
at the fix.
