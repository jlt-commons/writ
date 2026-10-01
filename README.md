# writ

writ checks plain Clojure against a spec of what the code is for. The spec
is the problem statement written so a machine can check it: signatures for
the public functions, and laws that say what their results mean. It lives
in its own namespace, and the code never mentions writ.

It is built for code an LLM writes. The spec is the intent: the problem's
states, the steps between them, and what each step means. An agent, or a
person, writes it first; then the implementation. writ is the gate
between them. Its report says what to fix: the rule that was broken, or
the law that failed, the smallest input that fails it, and the value each
side produced.

A spec is not a test suite. Tests pin down examples: this input gives that
output. A spec states what must hold for every input: the output is
ordered, and it has the same elements as the input. That is the meaning of
a sort, not a sample of it. writ also checks the spec itself. It rejects a
law that any implementation would satisfy, and it reports a function the
laws don't pin down, naming a trivial stand-in that would pass.

The static rules come from [Bend](https://github.com/HigherOrderCO/Bend):
pure code only, recursion that provably terminates, definitions in order,
types that fit. Behaviour is checked two ways. The laws run, through
[test.check](https://github.com/clojure/test.check), on inputs generated
from the spec's types. And writ proves them from the code: by rewriting
and induction, or by running the code on symbolic values and handing the
result to a solver. A proof holds for every input, not the ones a test
happened to try. Every proof is replayed by a small checker before it is
reported, and the solver's answers come with certificates that checker
verifies, so the search is never trusted. The report says which laws are
proved and which are only tested, and a spec can demand proof.

writ runs on [jolt](https://github.com/jolt-lang/jolt).

## The workflow

```
src/my/sort.clj           the implementation: plain Clojure, no writ
test/my/sort_spec.clj     the contract: spec, graph, refine, ann, law
test/my/sort_proof.clj    optional: lemmas and hints that help the prover
```

1. Declare the state graph. Every spec has one: the problem's states, as
   types -- refinements most often -- and the fns that step between them.
   It is the first thing a spec says. writ proves each of its edges, and
   checks that the code takes every step the graph names.
2. Say how the steps are wired: `flow` for the path data takes through a
   fn, `calls` for the layers it goes through.
3. State what each step means, as laws, and ask for proof with
   `(spec my.sort {:require :proved})`.
4. Read the plan back: `(spec/plan 'my.sort-spec)` prints the states,
   steps, signatures, laws and wiring from the spec alone, for a person
   to confirm before any code is written.
5. Write the implementation as ordinary Clojure.
6. Run the check. If it fails, the report says what to fix. If a law holds
   but is not proved, help the prover with a lemma or a hint in the proof
   namespace; don't weaken the law.
7. Keep the spec in the test suite, so it gates every change. A spec
   namespace is a clojure.test namespace: the test runner checks it.

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
  (:require [writ.spec :refer [spec ann law graph refine]]))

(spec my.sort {:require :proved})

(ann insert      [Nat (List Nat) -> (List Nat)])
(ann isort       [(List Nat) -> (List Nat)])

(defn ascending? [xs]
  (or (empty? xs) (apply <= xs)))

;; what makes a list sorted
(refine Sorted [xs (List Nat)] (ascending? xs))

;; the problem's states: a list goes in, a sorted list comes out, and
;; inserting into a sorted list keeps it sorted (`_` is where the state goes)
(graph sorting
  {:states {:unsorted (List Nat), :sorted Sorted}
   :edges  {:unsorted {[isort] #{:sorted}}
            :sorted   {[insert Nat _] #{:sorted}}}})

(defn occurrences [x xs]
  (count (filter #(= x %) xs)))

;; the graph already says a sort puts its input in order; it also
;; keeps every element, duplicates included
(law permutation (forall [x Nat, xs (List Nat)]
                   (= (occurrences x (isort xs)) (occurrences x xs))))

;; and insert adds exactly one x
(law insert-adds (forall [x Nat, xs (List Nat)]
                   (= (occurrences x (insert x xs)) (inc (occurrences x xs)))))
```

The check runs with the rest of the tests. `(spec my.sort)` also defines
`writ-check`, a clojure.test test in the spec namespace that runs
`(spec/check 'my.sort-spec)` and fails with the report's message, so
`(clojure.test/run-tests 'my.sort-spec)`, or any runner that loads the
namespace, checks the spec. A runner that finds test namespaces by name
has to be told about the `-spec` ones: with Cognitect's test-runner that
is `-r ".*-(test|spec)$"`, with Kaocha `:ns-patterns ["-test$" "-spec$"]`.

`{:test {:seed 42 :trials 200}}` passes options to that check, and
`{:test false}` leaves the test out, for a spec that is meant to fail or
one a test checks by hand:

```clojure
(ns my.sort-test
  (:require [clojure.test :refer [deftest is]]
            [writ.spec :as spec]))

(deftest sort-meets-its-spec-as-tested
  (let [r (spec/check 'my.sort-spec {:require :tested})]
    (is (:ok r) (:message r))))
```

The graph's edges are laws: `sorting:unsorted:isort` says every list
`isort` returns is `Sorted`, and `sorting:sorted:insert` that `insert`
keeps a sorted list sorted. Each step the graph names must also be taken,
by some input. If `insert` dropped a value equal to the head, the report
would read:

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
be too weak. `{:adequacy :mutants}` adds mutants of each fn's own source:
the fn with one operator swapped (`<` for `<=`, `inc` for `dec`, ...), an
integer one off, or an if's branches swapped. A mutant must pass writ's
static check, so it is well-typed and terminates, and it counts only when
some input tells it apart from the real fn; one that no input tells apart
is the same fn, and never a gap. For `sign`, whose laws say what it does
at positive and negative `n` but not at 0:

```
the spec does not pin down `sign`: every law still holds when it has 1 for 0 in (cond (pos? n) 1 (neg? n) -1 :else 0), and it differs from the real fn on {n 0}
```

A mutant the samples do not tell apart is run again at the input that
shows it: each law that calls the fn on its own variables is run with
them set to that input. If one fails there, the mutant is rejected, and
the miss was the data's. A survivor is then a gap in the laws, and the
report says so: `and no law tells it apart, even run there`. writ seeds
the numbers in the code, the large ones too, so a threshold of 5000 is
tried at 4999, 5000 and 5001.

A spec may give examples beside its laws: `(example price [6000] 12000)`
says `(price 6000)` is 12000. It is checked as a law, `example:price:1`.
It also asks the other laws to pin `price` down there: a stand-in that
agrees with `price` everywhere but at 6000 must break one of them, or the
report says no law but the example says what `price` returns there. An
example is checked against the laws, not the laws against code written
by the same hand.

The stand-ins that change the real result change it the ways a mistake
keeps its type: a number one more or one less, a collection without its
first or last element or with one added, a record with one field changed.

Each law of the spec's own is also judged alone: one that tells none of
the stand-ins of the fns it calls from the real ones, such as a law that
says only `(every? nat-int? (isort xs))`, is named in the report. On its
own it holds of a constant answer too.

Passing this check is necessary for a good spec, not sufficient.

## Writing a spec

A spec namespace requires `writ.spec` and uses these forms.

- `(spec target.ns)` names the namespace it constrains. It comes first.
- `(ann f [A B -> R])` gives fn `f` its parameter and return types. Every
  public fn needs one: a public fn with no `ann` fails the check, since
  nothing would check it. Sign it if the plan has it, or make it private
  with `defn-` if it is a helper. A private helper that recurses over a
  collection needs an `ann` too, because writ has to know the collection
  is finite to accept the recursion.
- `(ann f [A -> R] {:requires (fn [a] ...) :ensures (fn [a r] ...)})`
  says more than the types: what the arguments must meet, and what the
  result meets given them. See [Signatures that say more](#signatures-that-say-more).
- `(refine Name [x Base] pred)` is a type: the values of `Base` where
  `pred` holds. See [Refinements](#refinements).
- `(graph name {...})` is the problem's states and the steps between them.
  See [The state graph](#the-state-graph).
- `(data Name Ctor (Ctor2 FieldType ...) ...)` declares a datatype the
  target's values use. `(data Box [a] (Wrap a))` takes type parameters.
- `(law name proposition)` states a law.
- `(calls f [g ...])` states exactly which fns `f` calls, and
  `(calls f {:through [g] :not [h]})` what it reaches. See
  [The call graph](#the-call-graph).
- `(flow f [param ...] [link link ...] ...)` states the path data takes
  through `f`. See [Flows](#flows).
- `(machine name {...})` states that a fn steps a state machine by a
  transition table. See [Machines](#machines).
- `(assume ns/f [A -> R])` and `(assume name proposition)` state what the
  spec takes as given about code writ does not check. See
  [Assumptions](#assumptions).

A spec may define its own helper fns, like `ascending?` above. They run
only when laws run. A helper may not share a name with a public fn of the
target: a law's free name is read as the target's fn first, so the helper
would silently be replaced by the code it is meant to judge. writ rejects
the spec instead, and says which name to rename.

### Types

Built in: `Nat Int Bool String Char Keyword Symbol Float Double Unit Any`,
`(List T)`, `(Vec T)`, `(Set T)`, `(Map K V)`, `(Tuple T ...)`, `(Opt T)`
(a `T` or nil), records (see [Records](#records)), `(Index :key Record)`
(see [Collections of records](#collections-of-records)), and function types
`(-> A B R)`, of up to eight arguments. Declared types come from `data`.

`Float`, `Double` and `Any` hold no NaN; `Float!`, `Double!` and `Any!`
are the same with NaN among their values, and their generators produce
it, alone and inside vectors. Clojure's `=` says NaN is not NaN, so a law
that compares values of a `!` type with `=` is false at a NaN, and writ
says so when it finds one. `writ.spec/same` is `=` with NaN the same as
NaN, at any depth: compare with it where you mean the same value.

```clojure
(law a-binder-captures-any-value
  (forall [s Symbol, v Any!] (same (capture [:Bind s] v) {s v})))
```

`(List T)` means any seq: a list, a vector, a lazy seq or nil. Generated
inputs mix all four, so code that only works on one of them fails. `conj`,
for example, prepends to a list and appends to a vector.

A generated `String` is most often letters and digits, and now and then
any printable ASCII with tabs and newlines, so code that trims or splits
meets whitespace. A generated `Int` stays between `-max-size` and `max-size`, so -50 to 50
by default, and a `Nat` between 0 and `max-size`. A law quantified over
`Int` therefore never reaches a value like `-127`. When specific values
matter, such as a return code's sentinels, anchor each one with a law that
names it: `(law eof-sentinel (forall [e Bool] (= :eof (classify-read -127 e))))`.

A collection is at most `max-size` long, and one inside another collection
at most its square root, 7 by default, so a map of vectors stays near the
size rather than its square; the numbers inside it still range over the
whole size. A map, set or index whose key can take only a few values (a
`Bool`, an integer refinement such as `(< t 3)`, a data type of constants)
gets no more entries than its key can tell apart.

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

### Collections of records

A problem with many entities keeps them together, and its rules are about
all of them at once: no two members share an email. `(Index :id Member)`
is a map of `Member`s, each kept under its own `:id`, and `:unique
[:email]` says no two share an email (two with no email, nil, share
one):

```clojure
(refine Member [m {:id Nat, :email String}] true)
(refine Db [db (Index :id Member :unique [:email])] true)

(ann register [Db Member -> Db])

(graph registry
  {:start  [:db {}]
   :states {:db Db}
   :edges  {:db {[register Member] #{:db}}}
   :final  [:db]})
```

Generated values are built that way, keyed and with no field shared, not
filtered for it. A refinement of an Index is built the same way: a record
is kept only when the index with it still meets the refinement's
predicate, so a rule across the records, no two bookings of a room at
once, costs nothing to generate. The refinement checks the key and
unique fields in its predicate too, so the edge law `registry:db:register` says a registration
lands in a `Db`: keyed by id, no email twice. A `register` that forgets
to look at the emails fails it:

```
law `registry:db:register` fails for
  db     = {1 {:email "", :id 1}}
  member = {:email "", :id 0}
  a register from db must land in db
```

A rule across the records that the type cannot say goes in an invariant
or the refinement's predicate; `writ.spec/unique-by?` says no two of a
collection share a value of a fn. Such a rule is usually kept by
induction, and each edge may assume the invariants of the state it
leaves; see the invariants under [The state graph](#the-state-graph).

### Records

Most Clojure code keeps its entities in maps. A map literal of keyword keys
is a record type, each key with the type of its value:

```clojure
(refine Member [m {:id Nat, :email String, :points Nat, :nick (Opt String)}] true)
(refine Fresh  [m Member] (zero? (:points m)))

(ann join  [Nat String -> Member])
(ann award [Member Nat -> Member])

(law award-touches-only-points
  (forall [m Member, n Nat] (= (dissoc (award m n) :points) (dissoc m :points))))
```

A value of the record is a map with every key whose type is not `(Opt T)`,
each holding a value of its type. An `(Opt T)` key may be absent or nil.
The map is open: keys the record does not name may be there too, though
generated values carry only the named ones, an `(Opt T)` key now absent,
now nil, now set. `refine` names a record, as `Member` above, and carves
states out of it, as `Fresh`.

The code builds records as map literals and reads them with `(:k m)`,
`get`, `assoc`, `dissoc` and `{:keys [...]}` destructuring. The static
check follows the keys:

- A literal map where a record is expected must carry every required key,
  each value fitting its type:

  ```
  `join` returns {:email String, :id Nat, :nick (Opt String), :points Nat} but its body has type {:email String, :id Nat}: the body leaves out :points
  ```
- Reading a key the record does not name fails. The map may hold it, but
  far more often the name is misspelt:

  ```
  `award`: `m` is a record with keys :email, :id, :nick, :points, and has no key :point. Read one of its keys, or add :point to its type, as (Opt T) if it may be absent
  ```
- An `(Opt T)` key read is `(Opt T)`, not `T`, so returning it where a
  `T` is due fails with "it may be nil". A default does not change that:
  `(:nick m "")` is nil when `:nick` is there and nil. Write
  `(or (:nick m) "")`.
- `assoc` and `dissoc` on literal keys give the record with that key set
  or gone, so dissoc'ing a required key and returning the map fails too.

The prover reads `get`, `assoc`, `dissoc` and `contains?` on literal keys,
knows a record's key holds its type (so `(:points m)` is a `Nat`), and
takes a map destructure of a record as the record itself. The member laws
above are proved by rewriting. Symbolic evaluation runs on records too,
so an edge over a record state is proved never to throw, and the solver
finds a record no test generates, such as a member with more points than
any generated one. A record's value may hold keys the record does not
name, so a law that counts or lists all of its keys, or compares it with
a map built afresh, is never proved, only tested.

### Laws

A proposition is built from:

- `(= a b)`
- `(and P ...)`
- `(=> P Q)`, where cases in which `P` does not hold are skipped
- `(forall [x T, y U] P)`
- `(exists [x T] P)`
- `(throws? e)`, true when evaluating `e` throws (lazy seqs in what it
  returns are realised first). Refer it from `writ.spec` with the rest. An error writ raises, an argument or result that
  breaks a signature, is not counted: it is rethrown, and the law fails
  with it, since the law misuses the code rather than finding it throws.
- any other expression, which holds when it is truthy

A hypothesis no generated input meets, such as `(= a (* 3 (+ b 40)))` when
a generated `Int` stays within 50 of 0, tests nothing. writ then asks the
solver for inputs that meet it: where the law is false there, the report
gives the solver's counterexample, confirmed by running the code; where
the law is proved, the proof stands on up to three inputs the solver found
for the hypothesis, and the stand-ins are judged at them too. Only when
the solver finds none either does the law fail with "the hypothesis never
held".

A set of integers made by `range` is read as an interval: its members,
its count, whether it is empty, and its intersection with another range
come from its bounds, so a law like "two spans overlap when their unit
sets meet", `(seq (set/intersection (set (range s1 e1)) (set (range s2
e2))))`, is proved or refuted by the solver. A spec's alias of
`clojure.set` is read as `clojure.set`.

An `exists` over a `Nat` or `Int` whose body is bounds on it, with the
spec's own one-expression helpers read through, means the bounds meet:
`(exists [t Nat] (and (<= s1 t) (< t e1) (<= s2 t) (< t e2)))` holds
exactly when each lower bound is below each upper one: `(<= (+ s1 1) e1)`,
`(<= (+ s1 1) e2)`, `(<= (+ s2 1) e1)`, `(<= (+ s2 1) e2)`. writ reads it
that way, so a law of that shape is proved or refuted by the
solver, where a nested `exists` of any other shape is only sampled:

```clojure
(defn holds? [s t] (and (<= (:start s) t) (< t (:end s))))

(law overlap-means-a-shared-unit
  (forall [a Span, b Span]
    (=> (overlaps? a b) (exists [t Nat] (and (holds? a t) (holds? b t))))))
```

```clojure
(law reading-past-the-end-throws
  (forall [v (Vec Nat), i Nat] (= (throws? (at v i)) (>= i (count v)))))
```

A `forall` may range over fns: a variable of type `(-> Nat Bool)` is a
pure fn, each one answering the same arguments the same way, drawn at
random like any value. A law over them says what the code does with any
fn it is given:

```clojure
(law what-is-kept-passes
  (forall [p (-> Nat Bool), xs (List Nat)] (every? p (keep-where p xs))))
```

A generated fn in a counterexample prints as the calls it answered, `p =
(fn {0 true, 3 false})`.

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
more and no fewer. A plan often knows the layers but not every helper, so
the map form states reach instead:

```clojure
(calls handle {:through [normalize respond] :not [str/upper-case]})
```

`:through` names fns `handle` must reach, directly or through any chain
of the namespace's own fns; `:not` names fns it must never reach. A
reach that breaks the rule is reported with its path:

```
the call graph of `handle` is not the one the spec gives
  `handle` reaches `clojure.string/upper-case`, which the spec says it never does: handle -> normalize -> clojure.string/upper-case
```

The call graph is read from `f`'s source:

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

`f` may be a fn of another namespace, named through the spec's aliases.
That is how a spec reaches the effect shell, which writ doesn't check but
which is where the core gets called: `(calls server/app {:through
[core/handle]})` fails if the shell answers requests some other way. In
such a form, a simple name is a fn of that namespace.

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

### Signatures that say more

A type says what kind of value a fn returns, not how it relates to what
it was given. An `ann` can say that too:

```clojure
(ann take-upto [(List Nat) Nat -> (List Nat)]
  {:ensures (fn [xs n r] (<= (count r) n))})

(ann clamp [Int Int Int -> Int]
  {:requires (fn [lo hi x] (<= lo hi))
   :ensures  (fn [lo hi x r] (<= lo r hi))})
```

The fns take the signed fn's arguments, in its order, with the spec's
own names for them; `:ensures` takes the result last. Each `:ensures` is
the law `clamp:ensures`: on arguments of the parameter types that meet
`:requires`, the result meets it. It is tested, proved and cited like any
law, so it is a contract the prover can lean on in the laws after it.
While the laws run, a call whose arguments break `:requires` fails at the
call, whoever makes it, and a result that breaks `:ensures` fails where
it returns:

```
`clamp` requires (<= lo hi), but is called with [9 0 0]
```

### Refinements

A refinement is a type and a predicate:

```clojure
(refine Paddle [y Int] (<= 0 y (- H PH)))
(refine Ball   [b (Tuple Column Row Pace Spin)] true)
(refine Green  [l (Tuple Keyword Nat)] (and (= :Green (first l)) (<= (second l) GREEN)))
```

It goes wherever a type goes: in an `ann`, a `forall`, a graph's states,
another refinement. Its values are generated to satisfy it -- an integer
range is found once and sampled near its bounds and the spec's own
numbers, where code tends to break -- so a law never folds random inputs
into shape. The prover takes the predicate as a hypothesis, and the
static check sees the base type. `refine` also defines the predicate, as
`Paddle?`, for laws to use.

Other values are found by drawing from the base type and keeping those
that meet the predicate, and a predicate a random value rarely meets
starves: a receipt whose total is the sum of its items, a library whose
members' loan counts match the copies they hold. `{:build f}` names a fn
of the spec that makes any value of the base type one of the refinement,
and its values are drawn through it:

```clojure
(defn settle [r] (assoc r :total (reduce + 0 (:items r))))

(refine Receipt [r {:items (Vec Nat), :total Nat}] (= (:total r) (reduce + 0 (:items r)))
  {:build settle})
```

The predicate still decides: a built value it rejects is a mistake in
the builder, and the check says so.

When a fn returns a value outside its refinement, the report says which
rule it breaks. writ follows the predicate through the spec's helpers of
one expression, through `and` to the clause that fails, and through
`every?` and `not-any?` to the element that breaks them:

```
`lend` returns Lib, but returned {...} for arguments [...]: it breaks
(= (:loans m) (lent-to l (:id m))), at (:members l) key 0, m = {:id 0, :loans 0},
(:loans m) => 0, (lent-to l (:id m)) => 1
```

Every law that runs into such a value fails because of it, so the report
names the fn first, once, with the laws it explains, and shows one of
them in full: `` `lend` returns values outside Lib: fix it first; laws
that fail because of it: desk:lib:lend, lending-marks-the-copy ``. The
other failures follow.

Whichever way a refinement's values are made, writ sets one of their
integers, now and then, to a number the code or the spec mentions, or
one either side of it, and keeps the change when the value is still one
of the refinement. Those are the inputs that tell `<` from `<=`: a
member owing exactly the 500 at which borrowing stops. A law that is only
tested is also run where a sum or other computed term it compares with a
number equals that number or one either side, at inputs the solver finds.

### The state graph

Every spec declares its graph, and it comes first. Its states are types;
its edges are the fns that step between them:

```clojure
(graph signal
  {:start  [:green [:Green 0]]
   :states {:green Green, :yellow Yellow, :red Red}
   :edges  {:green  {[tick] #{:green :yellow}}
            :yellow {[tick] #{:yellow :red}}
            :red    {[tick] #{:red :green}}}
   :before [[:yellow :red]]})
```

An edge's key is the fn and the types of its other arguments. The state
is the first argument unless `_` marks where it goes: `[move-paddle Key]`
is `(move-paddle state key)` for every `Key`, and `[insert Nat _]` is
`(insert n state)`. An edge out of a tuple state may take a part of it
with `first`, `second` or `last`, which is how a fn that returns the next
state with something else leads back round: `{:result {[first]
#{:links}}}`. writ checks the graph four ways:

- **Data flow.** Each edge's fn must take its state's type and return its
  targets' type, by its `ann`.
- **Each edge is a law.** An edge into refinements is an obligation named
  for the graph, the state and the fn, `signal:yellow:tick`, run and
  proved like any law: the fn takes every value of its state into one of
  the states it names, and it never throws. The law is the target's
  predicate applied to the call, `(Sorted? (isort xs))` read as
  `(ascending? (isort xs))`, so it is proved the way the spec's own laws
  are. A step that breaks it is reported with the state it breaks on:

  ```
  law `signal:yellow:tick` fails for
    l = [:Yellow 5]
    a tick from yellow must land in yellow or red
  ```
- **Each step is taken.** An edge only bounds the code, and code that
  never leaves its state keeps every bound. So each target of an edge is
  also a law, `signal:green:tick->yellow`: some value of the state, and
  some arguments, land there. A signal stuck on green fails it:

  ```
  law `signal:green:tick->yellow` fails
    the graph says a tick can take green to yellow, but no generated green does
  ```
  Some steps no generated value takes, because their arguments must
  agree with each other: a reply answers a request only when it carries
  the alias the request made, and two values generated apart never share
  one. `:witnesses {[from to] [value arg ...]}` gives such a step an
  example, a value of `from` and the edge fn's other arguments, which
  the check tries before generating any:

  ```clojure
  (graph response
    {:states    {:msg Any, :answered Answered, :unanswered Unanswered}
     :edges     {:msg {[answer _ ReqId] #{:answered :unanswered}}}
     :witnesses {[:msg :answered] [[:a 1] [:Req :a :m :srv]]}})
  ```
- **The graph's own rules.** `:start` names a state, or `[state value]`
  with a value in it; every state must be reachable from it; `:final`
  states must be reachable from every state; `:never [a b]` says no path
  leads from a to b, and `:before [a b]` that every path from the start
  to b passes a.

What that adds up to: with every edge proved, `:never` and `:before`
hold for every run of the code, since a run only takes edges the graph
has. Reachability and `:final` are about the steps, each of which some
value of its state takes; they do not promise that a run from the start
gets there.

A state that is reached from the start and has no edges out must be
`:final`: absence of a way out is not the same as an end, so the graph
says which states a run may stop in. When a state reached from the start
can reach no final state, the report shows the loop that keeps it there:

```
graph `spin` breaks its own rules
  from :a no final state can be reached: it loops :a -> :b -> :a
```

**Invariants.** `(invariant g state [v] pred)` says what always holds of
a state's values, whichever edge they came in by. Every edge that may
land in the state carries the predicate in its law, a plain state
included, so a landing in `:hot` must be a `Hot` and hold it too, and a
`[state value]` start must satisfy it. Every edge out of the state may
assume it: a step keeps an invariant when it holds before the step, so
one that holds only by induction, such as an even count that climbs by
two, is kept, and with the start holding it every run does. A start
named by its state alone, `:start :hot`, may be any value of it, so
edges out of the start state then assume nothing; give the start a
value to have them. An invariant the state's own refinement already implies is
vacuous and fails, as a vacuous law does: say what a landing must keep
that the type does not.

```clojure
(invariant gauge :hot [g] (even? (second g)))
```

**Guards.** An edge can be taken only under a test. Its value is then a
map: `:to` the targets, `:when` a `(fn [state arg ...] test)` taking the
fn's own arguments in the fn's order, and `:else` what the step does when
the test fails, `:keep` (the default) to leave the state as it was, or a
state to land in:

```clojure
(graph account
  {:start  [:open [:Open 10]]
   :states {:open Open, :closed Closed}
   :edges  {:open {[withdraw Nat] {:to #{:open} :when (fn [a amt] (<= amt (second a)))}
                   [close] #{:closed}}}
   :final  [:closed]})
```

The edge law, `account:open:withdraw`, holds under the test, and so do
its steps. Three more laws come with the guard.
`account:open:withdraw:refused` says a refused withdrawal leaves the
account as it was: code that empties the account instead fails it.
`account:open:withdraw:when` says some value passes the test, since a
guard that never holds means the step can never be taken. And for a test
that is an `and`, `:when.1`, `:when.2`, ... say each clause fails while
the others hold. A clause that never fails on its own rules out nothing
the others do not: `(<= 0 amt)` on a `Nat` amount is such a clause.

**Actors.** Who may take a step is a guard on who is taking it. A graph
names the argument that acts, by its type, and the key of it that holds
its role; each edge says which roles may take it:

```clojure
(refine User [u {:id Nat, :role Role}] true)

(graph vault
  {:start  [:open [:Open 0]]
   :actors {:type User :role :role}
   :states {:open Open, :closed Closed}
   :edges  {:open {[deposit User Nat] {:to #{:open} :by #{:owner :clerk}}
                   [close User]       {:to #{:closed} :by #{:owner}}}}
   :final  [:closed]})
```

`:by` is a guard, joined with the edge's own `:when` if it has one (the
own guard's clauses come first, and the role test is the last clause), so
the laws of a guard come with it: a step by one of the roles lands where
the edge says, and one by anyone else is refused and leaves the state as
it was. A close a clerk can make fails `vault:open:close:refused`:

```
law `vault:open:close:refused` fails for
  user = {:id 0, :role :clerk}
  v    = [:Open 0]
  taken by anyone but :owner, a close from open must leave it as it was
  (close v user) => [:Closed 0]
```

`plan` prints, per role, the steps it may take. Without `:role` the
acting value is the role itself.

**Frames.** On a record state, an edge can say which keys its step may
change. Every other key must come through as it was, whether the record
names it or not:

```clojure
(graph membership
  {:states {:fresh Fresh, :active Active}
   :edges  {:fresh  {[award Pos] {:to #{:active} :changes [:points]}}
            :active {[award Nat] {:to #{:active} :changes [:points]}}}})
```

`membership:fresh:award:frame` is the law `(= (dissoc (award m pos)
:points) (dissoc m :points))`, run and proved like the edge's own, and an
award that also rewrites the email fails it:

```
law `membership:fresh:award:frame` fails for
  m   = {:email "", :id 0, :nick "", :points 0}
  pos = 1
  a award from fresh may change only :points, and must keep every other key as it was
  (dissoc (award m pos) :points) => {:email "!", :id 0, :nick ""}
  (dissoc m :points) => {:email "", :id 0, :nick ""}
```

An entry of `:changes` may also be a path into the state, whose parts
can be the step's own arguments, `(arg 1)` the first after the state:

```clojure
:edges {:lib {[lend Nat Nat] {:to #{:lib} :changes [[:copies (arg 2)] [:members (arg 1)]]}}}
```

says `lend` changes only the copy it lends and the member it lends to.
Everything else in the library, the other copies and members included,
stays as it was.

A `:when` may also name a fn of the spec, of one expression, that takes
the step's arguments in its order: `{[lend Nat Nat] {:to #{:lib} :when
lendable?}}`. The laws then use the same `lendable?`, so the guard is
said once, and each clause of its `and` still gets its own law.

A step whose outcome depends on its inputs may give its cases, each with
its own guard, targets and frame:

```clojure
:edges {:open {[withdraw Nat] [{:to #{:open} :when covered? :changes [:balance]}
                               {:to #{:overdrawn} :when short? :changes [:status :fee]}]}}
```

Each case has its own laws, `bank:open:withdraw#1` and `#2` with their
frames. Where no case holds the step is refused and keeps the state,
`bank:open:withdraw:refused`. No two cases may hold at once,
`bank:open:withdraw:cases`, so a spec that leaves a withdrawal of
exactly the balance to both fails at that input.

A graph may also give a model of its states: `:model {:view items
:steps {enqueue put, dequeue take-one}}`, where `items` is a spec fn
from a state to a simpler value, and each step fn named has a spec fn
that does the same to that value. Each such edge gets one law,
`queue:q:dequeue:model`: the step, then the view, equals the view, then
the model's step. A queue kept as two vectors is then said once, as one
vector, and a `dequeue` that takes from the wrong end fails it.

`:changes` goes with `:when` too, and then the frame holds under the
guard. It needs a record state and names only the record's keys.

**Runs.** `:runs N` walks N runs through the real fns from a `[state
value]` start, up to `:depth` steps each (default 20). At each step it
takes an edge chosen by the seed, with generated arguments. On every
other guarded step it looks for arguments the guard takes, drawing the
state's own integers and their neighbours too, since a guard like
`(= amt (:total o))` compares an argument with the state; the other steps
take their first draw, so refusals are walked as well. Each landing
must be in a state the edge allows (for a refused step, the state it
stays in or its `:else`) and hold that state's invariants, and every
final state reached by the graph must be reached by some run. When the
seeded runs miss a final state, runs are walked toward it, each step
taking an edge that brings it closer. A final state still not reached is
reported with the guard that refused every step, when one did. A run finds
what sampling each state apart can miss, a value only a long climb from
the start produces:

```
graph `counter` breaks on its runs
  a step takes [:High 95] to [:High 96], which is in none of :high
    walked :low -> :low -> ... -> :high
    (replay with {:seed 42})
```

States must say what sets them apart. Two states of the same plain type,
like `:unsorted (List Nat)` and `:sorted (List Nat)`, fail the check: a
value of one is a value of the other, so an edge between them checks the
type and nothing else, and the names say more than the graph does. Make
the state that means something a refinement, `(refine Sorted [xs (List
Nat)] (ascending? xs))`, and the edge into it is the law. For the same
reason an edge may not list a plain state beside refined ones: every
result is in the plain one. Define a refinement with the same helpers the
laws use, so the prover sees one vocabulary.

A spec for plain functions has a graph too: its states are the data the
problem moves through, and an edge into plain types is data flow only,
checked against the signatures. pong's graph has four states, one per
phase of a game, each a refinement of the game's tuple; its four edges
are proved from the code, so no sequence of key presses ever takes a
game out of them.

`(spec/mermaid 'my.spec {:graph 'signal})` draws a graph as a mermaid
`stateDiagram-v2`, and `(spec/plan 'my.spec)` prints it with the rest of
the plan; see [Other entry points](#other-entry-points).

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

A machine and a graph differ where it matters. A machine's states and
events are values, `:start` is a value, and its table is exact: every
pair is run, and a pair the table doesn't list must keep the state. A
graph's states are types, `:start` is a state's name (or `[state
value]`), and an edge says where a step may go and that it can: pairs
the graph doesn't list are unconstrained. Use a machine when the
meaning is a finite table, and a graph when the states are sets of
values.

### Flows

`calls` says which fns are called. It doesn't say what they are given: a
fn can call every layer the spec names and still hand the second one the
raw input, throwing the first one's work away. `flow` states the path the
data takes:

```clojure
(flow handle [req]
  [req normalize respond :result]
  [normalize :result])
```

The vector after the fn names its parameters, by position, so the spec
never depends on what the code calls them. Each chain after it is a path,
and every link must reach the next:

- `a` reaches fn `b` when some call the fn makes to `b` is passed a value
  that comes from `a`: from the parameter `a`, or from what a call to fn
  `a` returned, directly or through other calls.
- `a` reaches `:result` when what the fn returns comes from `a`. A
  branch's test counts, so a check that decides the answer reaches it.
- A lambda passed to a fn, as in `(map (fn [x] (step x)) xs)`, is given
  that call's other arguments, and so is a fn passed by name. A loop's
  bindings carry what each `recur` passes.

The check reads the fn's source. A flow that the code breaks names the
link:

```
the flow of `handle` is not the one the spec gives
  `respond` is never given anything that comes from `normalize`
  what `handle` returns does not come from `normalize`
```

A flow names only parameters and fns; a name that is neither, or a
parameter count that doesn't match, fails the check. Like `calls`, a flow
may be about a fn of another namespace, such as an effect shell. A fn a
flow names is a step of the plan, like a graph's edge fns.

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
 :flows       [{:fn handle :chains ["req -> normalize -> respond -> result"] :status :ok} ...]
 :graphs      [{:graph sorting :status :ok :states 2 :edges 2} ...]
 :machines    [{:machine screens :status :ok :states 6 :events 7} ...]
 :unspecified []                ; public fns with no ann: each fails the check
 :off-graph   []                ; signed public fns no graph, machine or flow names
 :message     "writ.spec: my.sort-spec against my.sort: ok\n  `insert`: ..."}
```

It works in three stages, and each runs only if the one before passed.

1. **Static.** writ reads the target's source from the classpath, puts the
   `ann` types on its `defn`s and checks it (see below). If this fails,
   `:static` carries the error and no law runs. Nor does one run when a
   helper of the spec shares a name with a public fn of the target;
   `:ambiguous` names it.
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
   with the reason, and `:stuck`: the goals the search could not close,
   deepest in the attempt that got furthest first, each with the
   induction case it was in and the facts it had. The report shows them
   under a law that needs proof; a lemma that proves such a goal from
   those facts closes it. With `{:explain true}`, each law the prover
   tried also carries `:attempts`, one entry a strategy in the order they
   ran, `{:name [:induct xs] :outcome :failed :fuel 3951 :ms 591}`, the
   outcome `:proved`, `:failed`, `:fuel` (it ran out) or `:rejected` (the
   checker refused its proof), and the report shows the stuck goals of
   laws that are only tested too. Each law's `:evidence` is `:proof` (proved,
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
`:failed`, plus `:missing` and `:extra` when it failed (`:unreached` and
`:reached` for the map form). Each `flow` gets an entry in `:flows`, with
`:errors` when it failed. A passing report lists the signed public fns
that no graph, machine or flow names, as `not a step of any graph or
machine`: a public helper is fine, but a reader should see it. Each `machine`
gets an entry in `:machines`; a failed one carries `:mismatches`, one
`{:state :event :expected :actual}` per pair the code gets wrong, and
`:errors` for the table's own rules.

Options: `:target` checks a different implementation against the same spec,
`:trials` is the number of test.check runs per law (default 100), `:seed`
replays a run (default random, reported per law), and `:max-size` is the
largest generated size (default 50). A law the prover does not prove gets
up to 900 more trials after its first 100, a hundred at a time with the
seeds after its own, within 20 seconds; `:more-trials {:trials n :ms t}`
changes that and `:more-trials false` turns it off. `:adequacy false` skips the third
stage, for example while a spec is still being written, and
`:prove false` skips the prover. `:require` sets the evidence every law
needs, in place of the spec's own. `:proof` names the proof namespace
(`false` for none), and `:fuel` gives the prover more rewrites per
attempt.

Proofs are cached in `.writ-cache/`, one file per spec. Each law's result
is kept under a key of everything its proof can rest on: the law, its
hint, the lemmas it may cite, the definitions it reaches (the fns it calls
and the fns they call, not the rest of the code), the plain data it names,
the signatures and data types, and writ itself. So a check that changes
nothing proves nothing again, and editing one fn keeps the results of the
laws that never reach it. The proof of each law is kept too: when a law's
key has changed, its last proof is replayed through the checker against
the code as it is now, and only if the checker rejects it does the search
run. A replayed proof is marked `:replayed`. Since the checker is what a
proof rests on, a stale or wrong proof in the cache can't make a law
proved. The contracts proved for the code are cached
apart, in one file per implementation, keyed on the code, its signatures
and data and writ, so editing a law or the proof namespace keeps them.
`:cache false` turns it off; `:cache-dir` puts it
elsewhere. Add `.writ-cache/` to `.gitignore`.

A report's `:timings` says where the check's time went, in milliseconds:
`{:static :tests :prover :more-trials :adequacy :graphs :total}`. Each
tested law carries `:test-ms`, the time its first trials took, and a bench
row carries it too.

A spec can build on another's proved laws:

```clojure
(spec my.app {:uses [my.sort-spec]})
```

checks `my.sort-spec` first (from its cache, when that holds), and each of
its laws that is proved is a lemma here, which a proof may cite by its
full name, `my.sort-spec/sorted`. Like a proof namespace's lemmas, they
are not laws of this spec, count toward nothing and judge no stand-in, so
a strong dependency can't make a weak spec look strong. A law of the used
spec that is only tested is not imported, and the report says so. Specs
may not use each other in a cycle.

### Requiring proof

A tested law has passed some trials; a proved one holds for every input.
By default a spec accepts either, and the report says which each law got:

```
writ.spec: my.sort-spec against my.sort: ok
  6 of 7 laws proved; tested, not proved: smallest-first (each on at least 1000 inputs)
```

A law that is only tested runs its first 100 trials and then up to 900
more, since tests are all it rests on. A failure among the extra ones is
reported with the seed that replays it in the first hundred.

Each trial also notes how the law's clauses came out: every comparison
in it, and every part of its hypotheses. A clause the first hundred saw
only one way is turned the other by the solver, under the law's
hypotheses, and the law run there. The extra trials stop once every
clause has gone both ways a few times, and a clause that never turned,
by the trials or the solver, is named:

```
law `spending-stays-within-the-limit`: (<= 0 (count (frequencies (:flags a)))) was never false in 1000 trials, nor at an input the solver found. ...
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

### The proof namespace

When a law holds but the prover can't find its proof, it needs a lemma or
a hint, and those don't belong in the spec: the spec is the contract, and
lemmas are how it is proved. They go in the proof namespace, found by
name (`my.sort-proof` for `my.sort-spec`) or given as check's `:proof`:

```clojure
(ns my.sort-proof
  (:require [writ.spec :refer [proof-of lemma hint]]))

(proof-of my.sort-spec)

(lemma insert-keeps-sorted
  (forall [x Nat, xs (List Nat)]
    (=> (my.sort-spec/ascending? xs) (my.sort-spec/ascending? (insert x xs)))))

(hint sorted {:induct xs :use [insert-keeps-sorted]})
```

A lemma is a law about the code: it is tested, and it must be proved, or
the check fails. Once proved, the spec's laws may cite it. It is reported
apart, it counts toward no law of the spec, and the adequacy check never
judges a stand-in by it, so a lemma can't make a weak spec look strong.
A lemma may be about clojure.core alone, such as what a bound on a list
says about a `filter` of it.

A proof namespace may define helpers for its lemmas with `defn`, such as
an invariant the code keeps. The prover reads them as it reads the
target's, and a helper that refers to the target's fns reads those of
the target under check.

A lemma's hypothesis may name a variable its conclusion doesn't. The
prover finds that variable's value in the facts of the goal at hand, the
way ACL2 does:

```clojure
(lemma none-below
  (forall [x Nat, v Nat, xs (List Nat)]
    (=> (and (every? #(> % v) xs) (<= x v)) (= (filter #(< % x) xs) ()))))
```

rewrites `(filter #(< % x) r)` to `()` wherever the facts say every
element of `r` is above some `v` with `x <= v`.

A hint steers the search and nothing more: `:induct` the variable to try
induction on first, `:vary` the other variables the induction hypothesis
holds at every value of (an accumulator a fold passes on), `:use` the
only lemmas and laws a proof may cite, `:strategy` one of `:symbolic`,
`:induction` or `:rewriting`, and `:fuel` the rewrites one attempt may
make. A proof a hint leads to is checked like any other.

`{:suggest true}` (or `{:suggest {:budget 40}}`, the attempts it may
spend on a law) asks the check to find what would prove each law that
stays tested, and print it as a form for the proof namespace; nothing is
added for you:

- first a hint: induction on each variable, with the others free in the
  hypothesis, each strategy alone, and more fuel, cheapest first;
- then a lemma, made from the goals the search got stuck on: the goal,
  under the facts that share its variables, with a call the goal and a
  fact both make (the one the induction hypothesis is about) taken as a
  variable. A candidate is offered only once it has passed its tests,
  been proved, and proved the law. Without `insert-keeps-sorted`, the sort
  spec's `sorted` gets that lemma back.

`writ.spec-demo.tree-proof` in the tests proves the tree's
`holds-a-sorted-set` this way: a `bst?` invariant, lemmas that `insert`
keeps it and that listing the tree after an insert is inserting into the
list, and a fold lemma with the tree varying.

### Proofs

After a `forall` law passes its tests, writ tries to prove it from the
code. It translates the law and the target's `defn`s into terms and
rewrites them to normal form. When that isn't enough, it tries structural
induction on each quantified variable, with the law at every smaller value
as a hypothesis:

- a list is nil, empty, or a head and a tail
- a `Nat` is 0 or p + 1
- a datatype has one case per constructor
- an integer `i` that a loop counts up to a bound `e`, such as
  `(count xs)`, is at or past `e`, or below it with the law at `i + 1`.
  That is induction on what is left, `e - i`, and it is tried first when
  a recursion of the code climbs on a law's integer. A scan that resumes
  from `start` is proved this way.

Within a case, the prover:

- splits an open integer comparison into its two outcomes, and
  substitutes an equality that holds, or that two facts pin down
- splits the test an induction hypothesis still needs, so the hypothesis
  can be used, and takes a boolean hypothesis that applies as facts
- closes a branch whose terms throw, since a law is about the inputs on
  which its terms return (not for a law that says nothing throws)
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
- **Sorting.** On a list of integers, `(sort xs)` and
  `(sort (distinct xs))` are a fold that inserts each element into the
  sorted list so far: the elements below it, it, the elements above it
  (at or above, when duplicates stay). `writ.prove.rewrite/model-check`
  runs the model against `sort` itself.
- **An accumulator.** A fold that grows an accumulator by addition from
  0, as a `loop` or a `reduce`, is first proved to give acc plus the fold
  from 0, from any integer acc, by induction with acc left free in the
  hypothesis. The law is then proved citing that.

A law proved earlier is a lemma for the laws after it: an equality
rewrites its left side to its right, anything else rewrites to true, when
its hypotheses hold.

A lemma holds only at its own types, and the prover's logic is untyped,
as ACL2's is, so a type is a hypothesis like any other. Each term a
lemma's variable takes must be shown to be of the variable's type: a
variable of that type is; an integer term is an Int, and a Nat when it
can't be negative; anything else must satisfy the type's recognizer,
which the prover builds from the spec's `data` and takes values apart
with the way the type's cases do. A signature is only a claim, so before
the laws, the prover proves each signed fn's contract from its code, as
ACL2s's `defunc` does: given arguments of its parameter types, it returns
a value of its return type. Then `(insert x t)` is known to be a `Tree`.
A set, a map or a fn has no recognizer, and takes only a variable of its
own type. An `Int` return is proved an integer, and a `Nat` return is then
proved not negative, so `(size t)` is an integer term the arithmetic
works with, known to be at least 0. The passes repeat until nothing new is proved, so a
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
  that tell them apart (`peek`, `vector?`, ...) are outside the model, so
  a law that needs them stays tested. `conj` and `into` onto a value the
  code makes a vector (`vec`, `mapv`, `subvec`, a vector literal, and
  `conj` or `into` onto one) add at its end; onto anything else, `conj`
  is outside the model.
- `take`, `drop`, `keep`, `mapcat`, `reverse`, `remove`, `not-any?` and
  `sequential?` are modelled on a list of any length, `subvec` on integer
  indexes, `nth` at an integer index, and `(range a b)` an element at a
  time once the facts decide `a < b`. A `for` with `:when` and `:let` is
  the `map`, `filter` and `mapcat` it means.
- A lazy seq is truthy before it is realised, so deciding one never runs
  its elements.
- `=` is Clojure's: sequentials compare element by element, and `1`
  never equals `1.0`. `Any` and `Double` range over values without NaN,
  as their generators do, so a law over them says nothing about `##NaN`,
  which is not `=` to itself; `Any!` and `Double!` take NaN in. A term
  equals itself when it only picks and arranges parts of NaN-free values;
  one that computes a float may be a NaN of none, and one of a `!` type
  may be one. `same` is reflexive whatever the value, and is `=` on
  values without NaN. The rewrite rules are checked against the runtime
  on values that include NaN.
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
- What the spec assumes about code writ does not check is tested on every
  check and named in every report; see [Assumptions](#assumptions).

The prover covers:

- `seq`, `first`, `rest`, `next`, `second`, `empty?`, `count`, `cons`,
  `list`, `vector`, `concat`, `filter`, `map`, `reduce` and `nth`
- `get`, `assoc`, `dissoc` and `contains?` on literal keys, and records
- `=`, integer arithmetic and comparisons, `integer?`, `if`, `case`, `let`
  and destructuring
- core fns passed as values, with `apply` of `<=`, `<`, `>=`, `>` and `+`,
  so a predicate like `(apply <= xs)` translates
- fn literals, `loop`/`recur`, and the target's and the spec's own
  `defn`s

A law quantified over fns is proved with the fn left unknown: the
prover never needs to know what it answers.

Anything else leaves the law tested, with `:unproved` saying why, for
example "outside the prover: `frequencies`". What the spec needs of such
a fn can be assumed, and the prover cites it; see
[Assumptions](#assumptions). A clojure.core fn it does not model is
assumed by its full name and read wherever the code calls it by its
plain name, unless the namespace excludes it from `clojure.core` or
refers another fn by that name. Its signature types every such call:

```clojure
(assume clojure.core/frequencies [(List Nat) -> (Map Nat Nat)])
(assume the-counts-add-up
  (forall [xs (List Nat)] (= (apply + (vals (frequencies xs))) (count xs))))
```

An assumption about a fn the prover does model is tested like any other,
but the model is what the prover reads.

### Symbolic evaluation and the solver

Rewriting splits a goal at every `if`, and a step fn with a dozen
conditions makes thousands of cases. So writ also runs the code once, on
symbolic values, the way [Rosette](https://emina.github.io/rosette/)
does: both branches of an `if` run, and their values merge under its
test. Integers merge into one value defined once, vectors of one length
merge element by element, and a data value whose constructor depends on
the branch is kept as a union of guarded values. Data values are split
into their constructors first, so each case is a small formula. What
comes out is one formula: the law holds, and, for a graph's edges, the
code never throws.

That formula goes to `writ.solve`, a solver written for writ in plain
Clojure: linear integer arithmetic (with `mod` and `quot` by a constant),
uninterpreted functions, and sets of unknown size as predicates. Two sets
are equal when an element the solver may choose is in both or neither, so
a law about every world of the Game of Life is one query:
`the-plane-has-no-favoured-place` is proved for every world, however
large, not sampled. The search is DPLL(T) with conflict-driven clause
learning, as SMT solvers do it: two watched literals, first-UIP learning
with non-chronological backjumps, VSIDS decisions with phase saving, Luby
restarts, and the simplex of Dutertre and de Moura as the theory, with
branch-and-bound and Gomory cuts for integrality. Clauses that share no
variable are solved apart first, as KLEE does. The search is not trusted.
An unsatisfiable formula comes with a certificate -- the learned clauses
in order, each justified by reverse unit propagation, a Farkas
combination or a cut, ending with the empty clause, as a DRUP or LRAT
checker reads a SAT solver's proof -- and `writ.solve.cert` verifies it,
as the proof checker does for every step. (`{:engine :dpll}` selects the
older tree search, whose certificates are case splits down to Farkas
combinations; both are checked.)

When the solver finds the formula invalid, its model is a counterexample.
writ turns it back into Clojure values and runs the law on them; if the
law fails there, that is the report, even when no test found it:

```
law `the-left-paddle-stops-the-ball` fails for
  b  = [3 3 -2 0]
  ly = 0
  ry = 4
  (held-by-left? ly (advance b ly ry)) => false
  (advance b ly ry) => [1 3 -2 0]
  (found by the solver, when no test did, and confirmed by running the code)
```

Symbolic evaluation covers the non-recursive code: arithmetic, `if`,
`case`, `let`, destructuring, vectors of known length, data values,
records, sets
built from literals and sets of unknown size filtered, mapped by a
translation, or tested for membership, and calls of pure core fns on
literal data. Recursion is left to rewriting and induction.

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
call graph; see [The call graph](#the-call-graph). `(spec/flow-facts 'my.ns
'f)` shows what `flow` reads: each call `f` makes, with where each
argument's value comes from, and where its result comes from.

`(spec/plan 'my.spec)` prints the spec as a plan for a person to read and
confirm, from the spec alone, so it works before the code exists: each
graph's states, with a refinement's predicate spelled out, and its steps
and rules; each signed fn with its signature, the laws that name it, its
flows and its call set; and the wiring the spec gives fns outside the
target, such as a shell's.

```
plan: my.pipeline-spec for my.pipeline

graph `request`
  states
    :raw       String
    :clean     Clean, a String where (= s (cleaned s))
    :response  (Tuple Keyword String)
  steps
    :raw -[normalize]-> :clean
    :clean -[respond]-> :response

fns
  handle  [String -> (Tuple Keyword String)]
    laws: handle-answers-with-the-cleaned-input, ok-exactly-when-short
    flow: s -> normalize -> respond -> result
    calls exactly: normalize, respond
```

`(spec/mermaid 'my.spec {:graph 'g})` draws graph `g` as a mermaid
`stateDiagram-v2`.

### Assumptions

The code a spec covers calls code writ does not check: `clojure.string`,
a library, another team's namespace. Calls into them pass the static
check, but the prover cannot read them, so a law that depends on what
they do stays tested. `assume` says what the spec takes as given:

```clojure
(ns my.slug-spec
  (:require [clojure.string :as str]
            [writ.spec :refer [spec ann law assume]]))

(assume str/trim [String -> String])
(assume str/lower-case [String -> String])

(assume trim-is-idempotent
  (forall [s String] (= (str/trim (str/trim s)) (str/trim s))))
(assume trim-and-lower-case-commute
  (forall [s String] (= (str/trim (str/lower-case s)) (str/lower-case (str/trim s)))))
```

An assumed signature types every call to the fn in the static check, so
code that hands `str/trim` a number fails there. While the laws run, the
fn is wrapped like a signed one, so a signature it does not keep fails
where it returns. Only the code's calls and the laws' are checked: writ's
own calls to the fn, and the dependency's calls to itself, are not the
spec's to type. The prover takes its result to be of its return type.

An assumed law is about such fns and never the target's: one that calls
a fn of the target fails, directly or through a spec helper or project
fn, since the target is what the spec checks. It
is tested against the real fns on every check, and a counterexample fails
the check:

```
assumption `trim-empties` does not hold of the code it is about for
  s = "0"
  (str/trim s) => "0"
```

The prover cites one that holds as it cites a lemma, but it is not proved,
so every report names what the spec assumes, and a proof names the
assumptions it cites:

```
writ.spec: my.slug-spec against my.slug: ok
  7 of 7 laws proved (5 for every input, 2 on particular values) (the spec requires proof)
  assumes, tested but not proved: clojure.string/lower-case [String -> String], clojure.string/trim [String -> String], trim-is-idempotent, trim-and-lower-case-commute
  law `cleaning-twice-is-cleaning-once` proved by rewriting, citing trim-and-lower-case-commute, trim-is-idempotent, ...
```

An assumption counts toward no law and judges no stand-in, like a lemma.
Each is an obligation, `assume.clojure.string/trim` and
`assume.trim-is-idempotent`, `plan` lists them, and `attest` counts an
assumption the earlier record did not make, or made differently, as a
weaker spec. Assume what the dependency documents, not what the proof
happens to need.

### What to ask

A spec is only as good as the decisions it records, and the code decides
every case whether anyone chose it or not. `(spec/elicit 'my.spec)` lists
the decisions the spec's types raise, for the person confirming the plan
to answer, and `plan` ends with them:

```
ask the spec's owner, before the code decides
  What should each give for an empty collection or string: nothing, a default, or a refusal?
    take-upto
  What should each do at zero, and with a negative number where one can arrive?
    clamp, clamp-digit, take-upto
```

Collections raise the empty case, integers zero and negatives, optional
values what absent means, floats precision and rounding, wherever they
sit in a type, so `(List Int)` asks about negative elements too, and each graph
what a run's whole life may hold: undoing, cancelling, repeating,
expiring. They are prompts, not failures, since a law over every input
may already answer one. Each answer is a law, a state or a step, or a
`question` until someone knows; `skills/writ/SKILL.md` has the full list
to go through.

### Open questions

`(question id "text")` records a question the spec does not answer yet.
Every report lists the open questions, and `plan` shows them, since a
spec with one is not finished. `(question id "text" {:blocking true})` is
one the next piece of work depends on: the check fails until the answer
is written into the spec and the question removed.

### Obligations and records

`(spec/obligations 'my.spec)` lists everything the spec obliges, from the
spec alone, as data an agent can keep track of: each law, signature,
`:ensures`, edge, step, guard and refusal, frame, invariant, graph rule,
run, flow, call set, machine, assumption and question, with an id (`law.permutation`,
`edge.account.open.withdraw`, `guard.account.open.withdraw.2`,
`frame.membership.fresh.award`, `ensures.clamp`,
`invariant.gauge.hot`, `final.account`), its kind and the signed fns it
names. A check's report has `:obligations`, each id with its status:
`:met`, `:failed`, `:unproved`, or `:open`/`:blocking` for a question.

`(spec/check 'my.spec {:record "path"})` writes a record of the check:
the spec, target and proof sources by SHA-256, each law as written with
the evidence it needs and got, the questions and each obligation's status.
Checks with the same seed write the same record. `(spec/attest old new)`
compares two records. Each side is a record, a path to one, or a spec
namespace, which is checked afresh rather than trusted. It reports each
way the later spec is weaker: a law removed or restated, its requirement
lowered (`:proved` to `:tested`), its evidence dropped (proved, now only
tested), another obligation gone, a blocking question no longer blocking,
a new or changed assumption, or a check that passed and now fails.

```clojure
(spec/attest "spec-record.edn" 'my.spec)
;; => {:ok false :weakened [{:law sorted :what :require-lowered}]}
```

A record also holds each `ann` and each refinement as written, so a
signature loosened or a refinement rewritten shows as `:changed`.

Changing the code never weakens the spec; a restated law its owner agreed
to is accepted by writing a new record.

A spec can hold itself to a record: `(spec my.sort {:baseline
"spec-record.edn"})`. Its check, and the test it defines, then fails
whenever the spec is weaker than the record, naming each way: `law
`permutation` is removed`, `the ann of `insert` is changed: was ...,
now ...`. An agent that edits the contract to get the code through is
stopped by its own test run. The owner writes the record, and writes a
new one to accept a change: `(spec/check 'my.sort-spec {:record
"spec-record.edn"})`.

### Laws that contradict

When a law fails, writ looks for another law about the same fn that no
code could satisfy along with it. At generated inputs it replaces the
fn's call by an unknown result, evaluates the rest of both laws, and asks
the solver whether any result meets both. It reports a pair only with the
solver's certificate that none does, checked, so the report is never a
guess from samples:

```
laws `rises` and `falls` cannot both hold: at x = 0, no value of (flip x) meets both, ...
  Fixing the code cannot help; the spec's owner must say which law is meant.
```

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
  of, and `writ.prove.check` the checker that replays every proof;
  `writ.prove.symbolic` runs code on symbolic values, and
  `writ.prove.smt` hands open goals to the solver
- `writ.solve`: the certifying solver for linear integer arithmetic and
  uninterpreted functions; `writ.solve.pre` turns formulas into clauses,
  `writ.solve.cdcl` (clause learning, the default) or `writ.solve.search`
  (the tree search) and `writ.solve.simplex` search, and
  `writ.solve.cert` checks certificates without searching
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

`jolt -M:bench DIR-or-spec-ns ...` (`./bin/bench` for the demo specs,
`examples/bin/bench` for the examples) benchmarks the prover:
`writ.bench/run` checks each spec with the proof cache off and makes a row
per law the prover tried, with the strategy that proved it, the rewrites
and the time; the table ends with how many laws were proved and which
strategies won. `--save FILE` keeps the rows, and `--baseline FILE` lists
the laws a change gained, lost, sped up or slowed down against them. It
never writes the proof cache.

The prover's knobs are one map, `writ.prove/default-config` (the fuel, how
deep case splits go, the strategy order, ...), which check's `:prover`
option overrides. `--tune '[{:depth 6} {:fuel 10000}]' DIR --held-out
DIR2` runs each config on a tuning corpus and a held-out one and reports,
against the default, the laws it gained and lost and its rewrites and
time; a config is a candidate for the default only when it loses no law
on either and costs no more. `cd examples && jolt -M:bench --tune ...
../test/writ/spec_demo --held-out test/fetch ...` tunes on the demo specs
and checks on the examples.

`test/writ/spec_demo/` holds the worked example: an insertion sort and a
binary search tree, each with a spec, one correct implementation and
several broken ones. Every broken one is rejected with a report that points
at the fix.
