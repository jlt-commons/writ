---
name: writ
description: >-
  Use when writing a writ spec -- the problem statement as a state graph
  and checkable laws about what code means and how it calls (writ.spec:
  spec/graph/refine/invariant/question/ann/data/law/assume/calls/flow/
  machine/plan/elicit/obligations/attest) -- or its proof namespace
  (proof-of/lemma/hint), or the plain Clojure implementation it
  constrains, or when reading a writ.spec report or any
  "Writ:" error (purity, termination, ordering, arity, types, tagged data,
  failing, unproved, vacuous or gapped laws, graph rules, call graph
  mismatches). Also for the annotated writ.defn surface (w/defn, ^:many,
  w/match, w/law, w/proof).
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

- The spec (`spec`, `ann`, `data`, `law`) is the contract. A person or an
  agent may write it; once written, it is the contract. Do not weaken a
  law, loosen an `ann`, lower a `:require`, or delete any of them to get a
  check to pass. If the spec looks wrong, say so and ask. Do not answer or
  downgrade a blocking `question` yourself. `(spec/attest record 'my.spec)`
  compares a recorded check with the spec now and names every way it got
  weaker.
- The implementation is yours. Change it until `check` reports `:ok`.
- If you are asked to write the spec, write the intent: see
  [What a spec should say](#what-a-spec-should-say).
- A report that fails is the next thing to fix. Read the whole message: it
  names the rule or law, the input, and the values.

## Writing a spec, in order

1. `(spec my.ns {:require :proved})` -- the namespace it constrains; ask
   for proof.
2. The state graph: the problem's states as types, refinements most
   often, and the fns that step between them. Every spec has one; write
   it before the laws. See [The state graph](#the-state-graph).
3. `ann` for each public fn. A public fn with no `ann` fails the check;
   a helper the plan doesn't name should be private (`defn-`).
4. The wiring: `flow` for the path data takes through each fn that
   composes steps, `calls` for the layers it must (or must not) reach.
   See [Flows](#flows) and [The call graph](#the-call-graph).
5. Laws for what each step means. Record anything the problem statement
   leaves open as `(question id "...")`; add `{:blocking true}` when the
   next piece of work depends on the answer. Never invent the answer.
6. Ask what the problem statement leaves to chance (see
   [What to ask](#what-to-ask)), then show the plan: `(spec/plan 'my.spec)`
   prints states, steps, signatures, laws and wiring from the spec alone,
   and ends with the questions its types raise. When a person asked for the
   feature, show it to them and have them confirm it before writing code.
7. Then the implementation. If a law holds but isn't proved, write a
   lemma or hint in the proof namespace (see
   [The proof namespace](#the-proof-namespace)); never weaken the law.

## What to ask

Code decides every case one way or another; a spec should say which way
someone chose. Before the plan is confirmed, go through these with the
spec's owner, and turn each answer into a law, a state or a step, or a
`(question ...)` when nobody knows yet. Never pick an answer yourself.

- The core method: what the result is, stated so two people would compute
  the same thing.
- Units and precision: what a number counts, how exact it must be, how it
  rounds.
- Order and ties: which comes first when two are equal, and whether order
  matters at all.
- Thresholds: whether a boundary value is in or out (`<` or `<=`).
- Empty and edge inputs: an empty collection or string, zero, a negative
  number, nil, the largest value that can arrive.
- Missing values: what an absent optional key or value means.
- Surplus and shortfall: too much, too little, not enough to go round.
- Scope: what the code is not responsible for, and who is.
- The whole life: whether what happens can be undone, cancelled,
  repeated, paused, or expire.

`(spec/elicit 'my.spec)` lists the kinds its types raise, with the fns or
graphs each is about; `plan` prints them last. Those are prompts, not
failures: a law over every input may already answer one.

## The state graph

```clojure
(refine Green  [l (Tuple Keyword Nat)] (and (= :Green (first l)) (<= (second l) GREEN)))
(refine Yellow [l (Tuple Keyword Nat)] (and (= :Yellow (first l)) (<= (second l) YELLOW)))
(refine Red    [l (Tuple Keyword Nat)] (and (= :Red (first l)) (<= (second l) RED)))

(graph signal
  {:start  [:green [:Green 0]]                 ; a state, or [state value]
   :states {:green Green, :yellow Yellow, :red Red}
   :edges  {:green  {[tick] #{:green :yellow}} ; [fn ArgType ...] -> targets
            :yellow {[tick] #{:yellow :red}}
            :red    {[tick] #{:red :green}}}
   :before [[:yellow :red]]})                  ; also :never [[a b]], :final [s]
```

- The state is the fn's first argument, unless `_` marks it:
  `[insert Nat _]` is `(insert n state)`. `[first]`, `[second]` or
  `[last]` takes a state out of a tuple state, so a fn that returns
  `[next-state reply]` can lead back: `{:result {[first] #{:links}}}`.
- `(refine Name [x Base] pred)` is a type: values of Base where pred
  holds. Use it in `ann`, `forall`, states, other refinements. It defines
  `Name?`. Refine the parts (a Paddle, a Ball) rather than folding random
  Ints into range inside laws.
- Each edge's fn must fit by its `ann`: the state's param (first, or at
  `_`) = the state's base type, the others the arg types; the return type
  = the targets' base type.
- An edge into refinements is a law named `graph:state:fn`: every value
  of the state goes, by the fn, into one of the targets, and the fn never
  throws. It is tested and proved like any law, and reads as the target's
  predicate of the call, `(ascending? (isort xs))`.
- Each target of such an edge is also a law, `graph:state:fn->target`:
  some value of the state lands there. A step the code never takes fails,
  so don't list targets "just in case"; list the steps the problem has.
- Two states of the same plain type fail the check (`:unsorted` and
  `:sorted` both `(List Nat)` say nothing apart). Make the meaningful one
  a refinement, defined with the helpers the laws use:
  `(refine Sorted [xs (List Nat)] (ascending? xs))`, and the edge into it
  is the sort's law. An edge may not list a plain state beside refined
  ones either.
- An edge into plain types of their own is data flow only, checked
  against the signatures. A spec of plain functions still has a graph:
  the data the problem moves through.
- An edge argument written `'name` is not a type but the spec's own value
  of that name, passed as is: `[scan (Vec Pattern) 'yes Nat]` hands
  `scan` the spec's `yes` guard, since a fn cannot be generated.
- `:tested {state "why"}` lets the edges out of a state off proof, as
  `{:require :tested :because "why"}` does for a law. A report says so when
  such an edge gets proved after all, so the marker can go.
- `:start`, `:final`, `:never`, `:before` are rules of the graph itself.
  With every edge proved, `:never` and `:before` hold for every run of the
  code. Reachability and `:final` say each step can happen, not that a
  run from the start gets there. A state reached from the start with no
  edges out must be listed in `:final`.
- `(invariant g :state [v] pred)`: what every value of the state holds,
  whichever edge it came by. Each edge landing there carries it, plain
  states included, and a `[state value]` start must satisfy it. Each edge
  out of the state may assume it, so an invariant kept by induction is
  kept; with a keyword `:start`, edges out of the start state assume
  nothing, since it may begin at any value. One the refinement already
  implies is vacuous and fails.
- A guarded edge: `{[withdraw Nat] {:to #{:open} :when (fn [a amt] (<= amt
  (second a))) :else :keep}}`. The `:when` fn takes the edge fn's own
  arguments, in the fn's order. The edge law and steps hold under the
  test; `g:s:f:refused` says a refused step keeps the state (`:keep`, the
  default) or lands in the `:else` state; `g:s:f:when` says some value
  passes the guard; for an `and` test, `g:s:f:when.N` says clause N fails
  while the others hold. Guard what the problem refuses, rather than
  folding the refusal into the targets.
- Who may act: `:actors {:type User :role :role}` on the graph names the
  argument that acts and the key holding its role, and `:by #{:owner}` on
  an edge the roles that may take it. It is a guard, joined after the
  edge's own `:when`, so a step by anyone else must be refused and keep
  the state; `plan` lists who may do what.
- A frame, on a record state: `{[award Nat] {:to #{:active} :changes
  [:points]}}`. `g:s:f:frame` says the step changes only those keys and
  keeps every other one, named by the record or not, as it was. It can go
  with `:when`, and then holds under the guard.
- `:runs N` (with `:depth D`, default 20) walks N seeded runs from a
  `[state value]` start through the real fns: every landing must be in an
  allowed state and hold its invariants, and every final state the graph
  reaches must be reached by some run.

## A spec

```clojure
(ns my.sort-spec
  (:require [writ.spec :refer [spec data ann law graph refine]]))

(spec my.sort {:require :proved})                ; the namespace it constrains

(ann insert [Nat (List Nat) -> (List Nat)])      ; one per public fn
(ann isort  [(List Nat) -> (List Nat)])

(defn ascending? [xs] (or (empty? xs) (apply <= xs)))   ; the spec's own
(defn occurrences [x xs] (count (filter #(= x %) xs)))  ; vocabulary

(refine Sorted [xs (List Nat)] (ascending? xs))

(graph sorting                                   ; its edges are the laws
  {:states {:unsorted (List Nat), :sorted Sorted} ; "isort sorts" and
   :edges  {:unsorted {[isort] #{:sorted}}         ; "insert keeps it sorted"
            :sorted   {[insert Nat _] #{:sorted}}}})

(law permutation (forall [x Nat, xs (List Nat)]
                   (= (occurrences x (isort xs)) (occurrences x xs))))
(law insert-adds (forall [x Nat, xs (List Nat)]
                   (= (occurrences x (insert x xs)) (inc (occurrences x xs)))))
```

- `(spec ns)` comes first; `(spec ns {:require :proved})` makes every law
  need a proof, not just passing tests. Prefer it for new specs.
- `(ann f [A B -> R])`: the parameter count must match the fn, which has a
  single arity. `(ann f [A B -> R] {:requires (fn [a b] test) :ensures
  (fn [a b r] test)})` adds what the arguments must meet and what the
  result meets given them; `:ensures` becomes the law `f:ensures`, and
  both are checked on every call while laws run. A private helper that recurses over a collection needs an
  `ann` too, or writ cannot tell the collection is finite.
- `(data Tree Leaf (Node Tree Nat Tree))`, or `(data Box [a] (Wrap a))`
  with type parameters.
- Types: `Nat Int Bool String Char Keyword Symbol Float Double Unit Any`,
  `(List T) (Vec T) (Set T) (Map K V) (Tuple T ...) (Opt T)`, `(-> A R)`,
  records such as `{:id Nat, :nick (Opt String)}`, `(Index :id Member
  :unique [:email])` (a map of records keyed by their :id, no two sharing
  an email, nil counting as one), and declared data. A fn type takes at
  most eight arguments.
  `(List T)` is any seq: list, vector, lazy seq or nil. `(Opt T)` is a T
  or nil.
  A generated `String` is mostly letters and digits, sometimes printable
  ASCII with whitespace. A generated `Int` stays within -50..50 and a `Nat` within 0..50 (the
  default `:max-size`), so a quantified law never reaches a value like
  `-127`. Anchor such values with a law that names them. A quarter of the
  time a `Keyword`, `Int`, `Nat` or `Any` is instead one of the literals the
  target's code mentions (with each integer's neighbours), and an `Any` is
  sometimes a vector tagged with one of its keywords, so a branch on
  `(= :normal reason)` or `(case (first ret) :reply ...)` is reached.
- A law is built from:
  - `(= a b)`
  - `(and P ...)`
  - `(=> P Q)`; a case where `P` does not hold is skipped
  - `(forall [x T, y U] P)`
  - `(exists [x T] P)`
  - `(throws? e)`: evaluating `e` throws, lazy seqs in its value
    realised. A signature broken by the law itself is rethrown, not
    counted. Refer it from `writ.spec`.
  - any expression, which holds when it is truthy

  A free name refers first to the target's public fns, then to the spec's
  helpers, then to clojure.core. A spec helper may not share a name with
  a target public fn: the check fails and says to rename the helper.
  A law may quantify over fn types: `(forall [p (-> Nat Bool)] ...)`
  draws pure fns, each answering the same arguments the same way, and a
  counterexample prints one as the calls it answered.
- `(calls f [g str/join])`: `f`'s direct calls are exactly this set.
  Multi-arity fns and macros are read too: a macro calls what it calls as
  it expands and what its expansion names. Name another namespace's fns
  in full (`ensemble.signal/on-signal`) when that namespace is not written
  yet, so the spec loads, and `plan` runs, before the code exists. A
  simple name is a target fn; a qualified one is a fn of another
  namespace, through the spec's aliases. Called or passed as a value both
  count. clojure.core, host members, self-recursion and locals that
  shadow a fn do not. `(calls f {:through [g] :not [h]})` states reach
  instead: `f` reaches `g` through any chain of calls, into the project
  namespaces `f`'s namespace requires as well (not clojure.* or jolt.*),
  and never reaches `h`. See [The call graph](#the-call-graph).
- `(flow f [param ...] [link link ...] ...)`: the path data takes through
  `f`. See [Flows](#flows).

## Assumptions

When the code calls something writ does not check (`clojure.string`, a
library, another namespace), say what the spec takes as given:

```clojure
(assume str/trim [String -> String])                 ; a signature, via the spec's alias
(assume trim-is-idempotent                           ; a law about such fns only
  (forall [s String] (= (str/trim (str/trim s)) (str/trim s))))
```

A signature types the calls statically and is checked where the fn
returns while laws run, every call, writ's own included. A law is tested
against the real fns every check and cited by the prover like a lemma,
without proof. An assumption may not call the target's fns, directly or
through a spec helper. Every report lists what is assumed, and
`attest` counts a new assumption as weakening the spec, so assume what the
dependency documents, not whatever closes a proof.

- ``assumption `x` does not hold of the code it is about`` - the claim
  about the dependency is false; fix the claim, not the code.
- ``assumption `x` calls `f`, a fn of target`` - state what the target
  does as a law instead.
- A law left tested as "outside the prover: `frequencies`" can rest on an
  assumption about it: `(assume clojure.core/frequencies [...])` and a
  law about it, which the prover then cites. The signature types every
  plain `frequencies` call in the code, unless the namespace excludes it
  from core or refers another fn by that name.
- ``assumes a signature for `ns/f`, which does not resolve`` - require
  the namespace in the spec and name the fn through its alias.

## The proof namespace

When a law holds but isn't proved, add what the prover needs in
`my/sort_proof.clj` (found by name for `my.sort-spec`), not in the spec:

```clojure
(ns my.sort-proof
  (:require [writ.spec :refer [proof-of lemma hint]]))

(proof-of my.sort-spec)

(lemma insert-keeps-sorted          ; a law about the code; must be proved
  (forall [x Nat, xs (List Nat)]
    (=> (my.sort-spec/ascending? xs) (my.sort-spec/ascending? (insert x xs)))))

(hint sorted {:induct xs :use [insert-keeps-sorted]})
```

- A lemma must hold and be proved, or the check fails; it then helps
  prove the spec's laws. It never counts as one of them, and never
  judges a stand-in, so it can't strengthen a weak spec.
- A lemma may be about clojure.core alone, and its hypothesis may name a
  variable its conclusion doesn't: the prover takes it from the goal's
  facts. `defn` helpers (an invariant such as `bst?`) may live in the
  proof namespace too.
- A hint: `:induct` a variable first, `:vary [acc]` to let the induction
  hypothesis hold at any acc (a fold's accumulator), `:use` only these
  lemmas and laws, `:strategy` `:symbolic` / `:induction` / `:rewriting`,
  `:fuel` more rewrites. It only steers the search.
- The prover reads the target and the project namespaces it requires, so a
  pure core split over several namespaces is proved as one. A value of
  type `Any` is modelled as an integer, a constant, a boolean, nil, or an
  opaque value that can only be passed along and compared. A numeric test
  or a lookup on an opaque value is some boolean or some value the solver
  may choose, which only adds models; arithmetic on one is left to
  testing. A vector literal is known to be a vector and a `list`, `cons`,
  `map` or `rest` result known not to be, so `vector?`, `sequential?` and
  `get` on them are decided. A constant's kind (keyword, symbol, string,
  char) is known, so `keyword?` and `symbol?` are decided too.
- Maps are modelled: literals, `assoc`, `dissoc`, `merge`, `get`, `(:k m)`,
  `(m k)`, `contains?`, `count` and equality by entries, keys symbolic or
  not; `keys` and `vals` are unordered, so `every?` over them works and an
  order-sensitive use gives up. A map of unknown size (a `(Map K V)`
  variable) is outside.
- A recursive definition is unfolded, exactly, while a literal drives it --
  a pattern walked to its end, a vector of known length -- up to a depth
  and a count; past them the law is left to testing.
- A branch that gives up is dropped when the solver shows its path cannot
  be taken under the law's hypothesis, so `(=> (not (vector? x)) ...)`
  proves even though the code's vector branch walks elements the prover
  cannot see. An unknown answer (`vector?` of an opaque value, its `first`)
  is the same each time it is asked of the same value.
- The usual reasons a law isn't proved: recursion that needs a lemma about
  a helper (write the lemma), a law about a recursive fn stated over its
  whole output where a pointwise statement would do, or a form outside
  the prover (the report names it; restate the law if you can).

## Machines

`(machine name {:step f :start s :transitions {s {e s'}} :final [..]
:never [[a b]] :before [[a b]]})` states that `f` steps a state machine by
the table. Use it when the code's meaning is a table: screens, protocol
states, lifecycles. `f` is run on every state x event (from its `ann` when
those are data with field-less constructors, or `:states`/`:events`); an
unlisted pair must keep the state. The table must reach every state from
`:start`, reach a `:final` state from every state, never lead from `a` to
`b` (`:never`), and reach `b` only through `a` (`:before`).

- ``(f s e) is x, but the table says y`` - the code is wrong for that
  pair; fix the code. If the table is what's wrong, say so.
- ``from s no final state can be reached``, ``a must never lead to b, but
  it does: ...``, ``b must be reached only through a, but ... avoids it``
  - the table breaks its own rules; that is the spec's owner's to fix.
- `(spec/mermaid 'my.spec {:machine 'name})` draws it.

## The call graph

Laws say what the code computes; `calls` says how it is put together.
Use it where the structure is part of the intent: a handler goes through
the layer that owns a rule (`respond` decides validity, so `handle` must
call `respond`, not `valid?`), a helper is reused rather than inlined, a
pure core never reaches an IO namespace. An implementation that inlines
or bypasses passes every law and still fails `calls`.

- Start from the code's actual graph: `(spec/call-graph 'my.ns)` returns
  `{f #{g ...}}` for any namespace, effect code included. It reads the
  source and checks nothing.
- `(spec/mermaid 'my.ns)` renders it as a mermaid flowchart;
  `(spec/mermaid 'my.spec)` draws the target with the spec's `calls`
  over it, marking unlisted calls `not in spec` and absent ones `missing`.
- The static rules use the graph whether or not a spec has `calls`:
  definitions refer only to those above them, so there are no cycles but
  self-recursion, and `scan` reports every caller of a fn writ cannot
  check ("it uses `f`, which writ cannot check").

## Flows

```clojure
(flow handle [req]                   ; handle's params, by position
  [req normalize respond :result]    ; req goes to normalize, its result to respond,
  [normalize :result])               ; respond's to the result; the answer uses normalize
```

A link is a parameter, a fn (what it returns) or, last, `:result`. `a`
reaches fn `b` when some call to `b` is passed a value that comes from
`a`, directly or through other calls; `a` reaches `:result` when the
return value comes from it, a branch's test included. Lambdas passed to a
fn get the call's other arguments, as do fns passed by name; loops carry
what `recur` passes. `calls` says which fns are called; `flow` says what
they are given, which catches a fn that calls every layer but hands one
the raw input.

Write a flow for each fn that composes steps: a handler, a `step` that
dispatches, a policy built from smaller rules. `f` may be a fn of another
namespace, such as the effect shell (`(flow server/app [req] [req
core/handle :result])`); there, simple names are that namespace's fns.
`(spec/flow-facts 'my.ns 'f)` shows what the check reads.

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
  constant, an argument passed through, the real result reversed,
  missing its first element, plus one, or swapped for another value of the
  return type, and, when every law fixes an argument to literals, one that
  agrees with the real fn on those literals and differs everywhere else.
  The fix is a law that the
  stand-in breaks, and that states intent: add `permutation` so that
  "always returns ()" fails. Never special-case the stand-in in the code.

Rejecting every stand-in is necessary, not sufficient. Still ask whether
the laws say everything the problem statement says.

## The implementation

Plain Clojure, with no writ require and no annotations. writ rejects:

- Effects and interop: I/O, atoms and refs, futures, `eval`, `throw`,
  `new`, `.method`, `reify`, static members such as `System/getenv` or
  `Math/abs` (use `abs`), reflection.
- Top-level forms other than `ns`, `comment`, `def` and `defn`: no
  `defmulti`, `defrecord`, `defmacro`, `declare` or bare expressions.
  Each fn has one arity.
- A reference to a definition further down. There is no mutual recursion,
  so put helpers first.
- Recursion that does not provably descend. Each recursive call or `recur`
  must pass a strict part of one parameter, under a test on it:
  - `(rest xs)` or `(next xs)` under `(seq xs)` or `(empty? xs)`, and only
    on a collection typed finite, which the `ann` provides
  - `(dec n)` under `(pos? n)`, or `(zero? n)` on a `Nat`; a chain
    `(dec (dec n))` needs each depth guarded
  - `(- n k)`, `k` a literal, under a comparison proving `n >= k`, such
    as `(if (< n k) base (f (- n k)))`
  - fields from destructuring or `first`/`nth` under a non-nil test,
    including a `case` on `(first t)`
  - a field of a field, `(rest (rest xs))` or a nested `match`, with each
    read guarded at its own depth; a test on a deeper read guards the
    reads above it
  - `[:Tag f1 f2]` rebuilt from a matched field's own fields, each at its
    own index, which is no larger than that field

  A test inside `and` counts in the then branch, and each test of an `or`
  is false in its else branch. Recursion with no structural measure
  (`(quot n 62)`) takes a fuel parameter first: `(loop [fuel 11, n n] (if
  (and (pos? fuel) (pos? n)) (recur (dec fuel) (quot n 62)) ...))`.

  Parameters before the shrinking one pass through unchanged, so
  accumulators go after it, in the parameters and in `loop` bindings.
  `doseq` and `for` expand to such loops; their collection needs a type
  too.
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

### Records

A map with keyword keys is a record type: `{:id Nat, :email String, :nick
(Opt String)}` is a map with those keys, each value of its key's type. An
`(Opt T)` key may be absent or nil; every other key must be there. Keys it
does not name may be there too. Name a record with a refinement, and
carve states out of it the same way:

```clojure
(refine Member [m {:id Nat, :email String, :points Nat, :nick (Opt String)}] true)
(refine Fresh  [m Member] (zero? (:points m)))
```

The code builds and reads records as plain maps: literals, `(:k m)`, `get`,
`assoc`, `dissoc` and `{:keys [...]}` destructuring. The static check reads
them by key: a literal must carry every required key with a value of its
type, a read must name a key the record has, and an `(Opt T)` key read
may be nil, so it is not a `T`, default or not: `(:nick m "")` is nil when
the key holds nil; write `(or (:nick m) "")`. The prover works through
`get`, `assoc`, `dissoc` and `contains?` on literal keys, and symbolic
evaluation runs on records, so an edge over a record state is proved
never to throw.

## Running the check

```clojure
(require '[writ.spec :as spec])
(spec/check 'my.sort-spec)                        ; report map
(spec/check 'my.sort-spec {:seed 42})             ; replay a failure
(spec/check 'my.sort-spec {:target 'my.sort2})    ; same spec, other impl
(spec/check! 'my.sort-spec)                       ; throws with the message
(spec/sample '(List Nat) {} 5)                    ; what a type generates
(spec/scan 'my.ns)                                ; which fns a spec could cover
(spec/call-graph 'my.ns)                          ; {f #{g ...}}, read from source
(spec/mermaid 'my.spec)                           ; the graph, with the spec's calls
(spec/mermaid 'my.spec {:machine 'm})             ; a machine's table as a state diagram
(spec/mermaid 'my.spec {:graph 'g})               ; a state graph as a state diagram
(spec/plan 'my.spec)                              ; the plan, for a person to confirm
(spec/flow-facts 'my.ns 'f)                       ; what `flow` reads from f
(spec/instrument 'my.sort-spec)                   ; runtime arg/return checks
(spec/obligations 'my.spec)                       ; every obligation, with ids, from the spec alone
(spec/check 'my.spec {:record "rec.edn"})         ; write a record of the check
(spec/attest "rec.edn" 'my.spec)                  ; how the spec got weaker since the record
```

`(spec my.sort)` defines `writ-check`, a clojure.test test that runs the
check, so the test runner checks the spec namespace with no wrapper
(a runner that picks namespaces by name must match `-spec` too).
`{:test {:seed 42}}` passes check options; `{:test false}` drops it.
By hand: `(let [r (spec/check 'my.sort-spec)] (is (:ok r) (:message r)))`.
Other options are `:trials`, the test.check runs per law (default 100),
`:max-size`, the largest generated size (default 50), and
`:adequacy false`, which skips the gap check while a spec is being drafted.

## Reading a report

`:static` fails first. A static failure is a single `Writ:` message, and no
law runs until it is fixed. After that, each law has a `:status`:

- `:vacuous`: true of any implementation; the spec must change.
- `:proved`: passed its tests, and the prover derived it from the code for
  every input, and the proof checker replayed the derivation. `:proof`
  says how; `:lemmas` names the other laws it cited. Proved laws are
  lemmas for each other, in any order, so a spec whose laws build on each
  other (`insert-keeps-sorted`, then `sorted`) gets more of them proved.
- `:evaluated`: a law with no quantifiers, run once.
- `:tested`: passed test.check's trials. This is evidence, not proof.
  `:unproved` says why the prover did not prove it: a form outside its
  model (`conj` onto a non-vector, `frequencies`, most string fns), the
  proof checker rejecting the
  proof (a writ bug; report it), or no proof found. That is not a failure.
  A law written with modelled forms and the spec's own helpers is more
  likely to be proved.
- `:witnessed`: an `exists` law, and a value was found.
- A failure "found by the solver, when no test did" is a real
  counterexample: the solver found values that break the law, and running
  the code on them confirmed it. Fix the code at those values.
- `graph `g`: ... ` lines: edges proved, each of their steps taken, and
  edges checked as data flow; `graph `g` breaks its own rules` is the
  graph's own `:never`, `:before`, `:final` or reachability failing; fix
  the graph or the code, whichever is wrong, and say which.
- `not a step of any graph or machine: f` on a passing report: a signed
  public fn the plan doesn't place. Fine for a helper laws need to name;
  otherwise it belongs on the graph or in a flow.
- ``declares no state graph``: add the graph first.
- `:lemmas` in the report: the proof namespace's lemmas; each must be
  `:proved`.
- `:unproved`: the spec (`(spec ns {:require :proved})`) or the law
  (`{:require :proved}`) requires proof, and the law is only tested. Get
  it proved: restate it with forms the prover models, or add the lemma it
  needs as its own law. Only if it truly cannot be proved yet, mark the
  law `{:require :tested :because "why"}`; the reason shows in every
  report.
- `:failed`: see the message.

Each law also has `:evidence`, `:proof` (proved, evaluated, witnessed) or
`:test`, and the report's `:proof` counts them:
`{:require :tested :proved 6 :general 4 :tested 1 :laws 7}`. `:general`
is how many of the proved laws are `forall` laws, true for every input;
the rest hold on particular values (a closed law, an `exists` witness), and
the summary line says so: `6 of 7 laws proved (4 for every input, 2 on
particular values)`. A spec whose proofs are mostly particular values says
little beyond its examples, however many laws it proves.

A passing report lists, per signed fn, how many laws call it and how many
stand-ins of each kind they rejected:
`` `classify-read`: 5 laws, 3 impostors rejected (2 constant, 1 perturbed) ``.
Only constants rejected, or no fn laws at all, means the spec barely
touches that fn even though it passed.

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
- ``the call graph of `f` is not the one the spec gives`` - `f` calls a
  fn the spec does not list, or does not call one it lists, or (map form)
  does not reach a `:through` fn or reaches a `:not` one, with the path.
  Route the call through the named fn (don't inline it, don't skip a
  layer). If the graph in the spec is wrong, say so; don't edit `calls`
  to match.
- ``the flow of `f` is not the one the spec gives`` - ``` `b` is never
  given anything that comes from `a` ``` means pass `b` what `a`
  returns (or the parameter `a`), not something else; ``` `f` never calls
  `b` ``` means the step is missing; ``what `f` returns does not come from
  `a` `` means `a`'s result is computed and dropped. Fix the wiring.
- ``law `g:s:f->t` fails ... the graph says a f can take s to t, but no
  generated s does`` - the code never takes that step. Usually the code
  is stuck (a missing transition); if the step truly cannot happen, the
  graph is wrong: say so.
- ``graph `g`: :a and :b are both T, so nothing tells them apart`` - make
  one (or both) a refinement that says what it means.
- ``` `x` is defined by the spec and by ns ``` - rename the spec's helper;
  a law would otherwise judge the code with the code.
- ``` `f` is public, but the spec gives it no signature ``` - sign it if
  the plan has it; make it private (`defn-`) if it is a helper.
- ``the spec says `f` calls `g`, but ns defines no fn `g` `` / ``the spec
  gives `f` a call set, but ns defines no fn `f` `` - define it or fix
  the spelling; the spec names the structure.
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

- ``graph `g` breaks on its runs`` - a run from the start, through the
  real fns, left the graph, broke an invariant, or never reached a final
  state. The path and seed replay it. Fix the code at that value; if no
  run reaches a final state only because runs are short, raise `:depth`.
- ``invariant `g :s` is vacuous`` - the state's refinement already says
  it; state what a landing must keep that the type does not.
- ``law `g:s:f:refused` fails`` - where the guard fails, the code changed
  the state; a refused step must leave it as it was (or go to `:else`).
- ``the guard of f from s never holds`` / ``clause ... never fails on its
  own`` - the guard is wrong or has a clause that says nothing; that is
  the spec's owner's to fix.
- ``the spec is not finished: open question `q` blocks ...`` - ask the
  spec's owner; write the answer in as laws or states, then remove the
  question.
- ``laws `a` and `b` cannot both hold`` - no code satisfies both; the
  solver shows it. Do not change the code: ask which law is meant.

- ``writ bug: law `x` was proved (...) but a test refutes it`` - the
  prover is wrong, not your code. Report it with the seed, and rerun with
  `{:prove false}` meanwhile.

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

### Records

- ``` `m` is a record with keys :email, :id, and has no key :point``` -
  a misspelt key, or one the type should name. Add it to the record, as
  `(Opt T)` if it may be absent.
- ``returns {...} but its body has type {...}: the body leaves out :points``
  - build the map with every key the record requires.
- ``:points is Nat, but the body gives String`` - that key's value has the
  wrong type.
- ``returns String but its body has type (Opt String): it may be nil`` -
  an optional key was read, and it may hold nil even with a default.
  Write `(or (:nick m) "")`, or branch on it.

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
- ``argument N before the shrinking one must be passed unchanged; put `xs`
  first in the parameters`` (or ``the `loop` bindings``) - do what it says:
  the accumulator rides after the shrinking one.
- ``a macro's loop in `f`, such as a `doseq`, does not descend`` - the loop
  is the macro's, not yours; the message names the collection it walks.
  Usually that collection needs a finite type from `ann`.
- ``is not supported: in the code a spec covers, writ checks def and defn
  forms only`` - `defrecord`, `defmacro`, `defmulti` and the like cannot sit
  in the target; `scan` lists them. Move them out, or leave that namespace
  unspecified.
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
discipline on top of the rules above. Its `w/law` forms need a `w/proof`
gate that proves only identities, like `(= (status req s) (status req s))`;
a spec namespace rejects those as vacuous. Don't copy them into a spec.

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
cd examples && jolt -M:test       # the example programs and their specs
```

When a test run disagrees with a direct `jolt -e` of the same code, clear the
AOT cache before debugging. That is a known jolt issue, not a writ bug.

`test/writ/spec_demo/` holds worked specs, a sort and a tree, each with
broken implementations and the reports they produce. `examples/` has four
programs on real libraries (raylib pong and life, a ring-chez URL
shortener, an http-client fetcher), each a pure core, a spec, an effect
shell and broken cores; its README walks through what each report says.
Model a new spec on those.

## Source map

- `writ.spec` spec namespaces, law checking with test.check, instrument
- `writ.prove` proofs of laws from the code: `.term` the value model,
  `.rewrite` the rules (checked against the runtime), `.translate` Clojure
  to terms
- `writ.book` runs every rule over a namespace's forms
- `writ.check` quantities, termination, ordering, effects, arity
- `writ.types` types and tagged data, `writ.kind` well-kindedness
- `writ.lower` the AST, `writ.uses` occurrence analysis
- `writ.match` `w/match`, `writ.norm` conversion behind `refl`,
  `writ.law` propositions and the proof gate
- `writ.defn` the annotated macros, `writ.core` its entry points
