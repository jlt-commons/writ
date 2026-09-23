# Writ examples

Worked examples of the writ discipline: ordinary Clojure that also carries the
static guarantees writ checks. Each example is a **book** -- three files in one
directory:

- `main.clj` -- the implementation. Ordinary Clojure, plus writ's annotations
  (`w/defn`, `w/data`, `w/match`, `:-` types, `^:many`, `^:writ/descend`).
  Every `w/` macro expands to a plain `clojure.core` form, so this file *is* a
  normal Clojure file; writ just also checks it.
- `LAWS.clj` -- the spec. The equations the implementation must satisfy.
- `PROOF.clj` -- the proofs, plus `verify`, which reads the three files and runs
  the book through writ's rule engine.

Implementation and proof stay apart: `main.clj` never mentions a law, and
`LAWS.clj`/`PROOF.clj` never contain implementation logic.

These books use the older annotated surface, `writ.defn`, not the spec
namespaces (`writ.spec`) that the top-level README teaches. That matters
most in `LAWS.clj`. Laws like `(= (status req s) (status req s))` or
`(= 201 201)` are there because the `w/proof` gate proves identities, and
they say nothing about what the code does. `writ.spec` rejects exactly that
shape as vacuous, so don't model a spec's laws on these files. The books
are being ported to spec namespaces.

## This is a standalone jolt project

It has its own `deps.edn` and depends on writ through `:local/root ".."`, so it
runs on its own:

```sh
cd examples
jolt -M:test      # or ./bin/test
```

That checks every book below. `examples/test/examples_test.clj` calls each
book's `verify` and asserts `{:ok true}`, so a failure is a real rule violation
in the example, not a compile error.

## The examples

Ported from `/Users/yogthos/src/bend/demos`. Every demo there has a book here:
the six `proof_*`/`pure_*` were the first port, the five `app_*` and five
`io_*` follow. The `app_*`/`io_*` demos draw windows and talk to sockets, and
writ has no effect types, so each book carries the demo's *pure* core -- the
same line bend's own LAWS.bend draw.

- `proof_numerics` -- arithmetic identities (additive and multiplicative
  units, literal arithmetic) as laws, each discharged by `refl`.
- `proof_typed_eval` -- a tiny expression evaluator (`ELit`/`EAdd`) with laws
  about its result. bend's demo is intrinsically typed (`Expr<-t>` with
  equation fields, a type-returning `Val`, `opt`, `IsZero`/`If`); writ has no
  indexed families or equation fields, so only the untyped core is here.
- `proof_insertion_sort` -- insertion sort over a `NatList`, with a count law.
- `pure_par_sum` -- the fork/join tree (`pow2`/`sum`) and the sequential loop
  (`seq`) it is proved equal to.
- `pure_par_sort` -- the leaf sum of a binary tree, the quantity bend's bitonic
  sort is proved to preserve. The sort itself (`gen`, `mix`, `flow`, the
  depth-indexed `Tree(d)`) is not ported: it needs an indexed family.
- `pure_hvm5_mini` -- the pure core of the HVM5 evaluator: the source cursor,
  the packed run words, name codes, and the book depth.
- `app_pong_game_2d` -- the event fold that reads a quit, and the key-state
  fold where the last press wins.
- `app_triangle_2d` -- a 2D point, and the bounding-box area the demo scales by.
- `app_ray_tracer_3d` -- the vector dot product, and the frame's pixel count.
- `app_slash_boss_3d` -- shifting a 3D position, and the quit event.
- `app_win_is_bug_2d` -- the dead/alive cell rule, and a generation's live-cell
  population.
- `io_hello_world` -- bend's demo is one `IO.print` with no pure part; the book
  holds an invented stand-in so it is not empty.
- `io_http_fetch` -- the response walker that scans for the first blank line and
  returns the body after it.
- `io_http_server` -- the request fold that settles on a status code.
- `io_tcp_echos` -- the byte-for-byte line echo, and the last byte read.
- `io_rollback_netcode` -- the rollback buffer: push a `Set`, pop it back off.
- `theory_kinds` -- from `paper/BendTT` rather than a demo: the kind rule that
  makes reuse sound (a binder may be `^:many` only when its type has kind
  `Data`), the product types `(Tuple ..)`/`(List ..)`, the multi-value return
  `(& ..)`, and a law surface with hypotheses, conjunctions, universals and
  existentials.
- `theory_discipline` -- from the parity review rather than a demo: the rules
  that review closed. Local and pattern binders carry quantities (`^:many`
  where a value is reached twice), recursion is marked
  `^{:writ/descend true}` and every recursive call -- `recur` included --
  shrinks, a match scrutinee is a parameter or pattern binder (never a
  computed value), parametric types are matched once instantiated
  (`(Box Nat)`) and reuse over `(Box (-> Nat Nat))` is rejected by the kind
  rule, laws are cited only after their own proof, and defs reference earlier
  defs only.

## What the gate discharges (and what it does not)

The LAW gate reads a small proof language. A law states a proposition built
from `=`, `and`, `=>`, `forall` and `exists`; a proof discharges it with `refl`,
`pair`, `(fn [..] ..)`, or `(witness t pf)`, and may cite another law by name as
a lemma. `refl` closes an equality whose two sides are `norm/convertible?`.

`writ.norm` reduces let bindings and applied fns over values, `if` and
`case` over literals, arithmetic and comparison on literals, and the
additive/multiplicative identities `(+ x 0)` and `(* x 1)` when `x` is a
number (a `forall [x Nat]` binder, or a call to a book fn declared to return
a number). It keeps Clojure's strict evaluation, compares up to renaming
binders, and treats a throwing term as equal to nothing. It does not do
induction, and it knows nothing about `drop`, bit operations, or the
examples' own functions.

So each `LAWS.clj` is honest about the line between what is proved and what is
stated. bend's own laws -- `tree_is_seq`, `mix_leaves`, `drop_drop`, `at_drop`,
`run_push_pop`, `name_round_trip`, `book_depth_fits`, ... -- are recorded in the
law namespace's docstring as the spec the code exists to meet; the `w/law`
forms record the identities the gate actually discharges. Where an example's
algorithm is ported, it is ported to be recognisable, not to carry bend's
induction proofs, which writ does not have.
