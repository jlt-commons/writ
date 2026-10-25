# Replayable Proof Evidence Design

## Intent

Writ already replays newly found proofs and old traces loaded after a semantic cache miss. The review found two remaining trust shortcuts: an exact cache-hit returns a cached success without replay, and cached function-contract rules have no traces. Rainbow's useful rule is that loading evidence always re-enters the checker. This project adopts that rule, then makes evidence portable and its assumptions visible.

## Goals

1. Replay every cached law proof and function contract on every check.
2. Export self-contained proof bundles and verify them without project code, tests, or proof search.
3. Report each law's actual transitive assumptions and compare them during attestation.
4. Retrieve existing proved lemmas by normalized proposition shape under an explicit assumption policy.

## Non-goals and anti-goals

- Do not adopt Rainbow's dependent-type kernel, de Bruijn terms, universe system, or proof format.
- Do not make retrieval, content hashes, cached reports, or derived rules trusted evidence.
- Do not rerun tests or project code during bundle verification.
- Do not treat assumed laws/signatures or runtime-only evidence as replayed proofs.
- Do not add dependencies, Z3, or a second proof-checking semantics.

## Constraints and trust boundaries

`writ.prove.check` remains the only replay authority. Ordinary `spec/check` may recover from invalid evidence by searching again. Bundle verification uses `:replay-only`, so invalid evidence is rejected and never triggers search or counterexample search. Old cache entries without traces are misses. Assumptions remain explicit external trust.

Work uses jolt and the existing dependencies. The implementation stays on `feature/replayable-proof-evidence`; Rainbow and the untracked `blog.md` are untouched.

## Design

### Cache replay

A cached law success supplies only a trace candidate and a `:cached` marker. `prove-law` must replay it; missing or rejected traces cause ordinary fresh search. Failed-search results remain performance hints.

`prove-contracts` returns `{:rules :traces :replay-errors}`. Cached rules are never consumed directly. Each contract goal is regenerated with the same definitions, types, signatures, and earlier accepted contracts, and its trace is checked. Replay-only omits invalid contracts; ordinary checking searches for replacements.

### Proof bundles

A schema-1 EDN bundle contains pure translated prover inputs, contract traces, law traces, dependency bundles, source hashes for audit, explicit assumptions, and runtime-only evidence separated from replayed claims. A deterministic content ID covers the bundle but is only an integrity check, never a substitute for replay.

Canonical encoding uses explicit type tags, deterministic map/set ordering, and UTF-16 code units for strings, avoiding UTF-8 replacement collisions for unpaired surrogates. It supports every literal occurring in prover inputs.

Law evidence contains no functions, delays, atoms, or callbacks. Alpha-equivalent laws proved through an earlier law are checked alias entries. Every cited lemma must match an earlier verified entry or a listed assumption. Dependencies replay before dependents. `spec/check` accepts `:bundle path`; `writ.bundle/verify` accepts a path or map.

### Per-law assumptions

Direct use comes from checker `:lemmas-used`, not source occurrence or report strings. Signature IDs are `assume.<qualified-fn>`; assumed-law IDs are `assume.<spec-ns>/<law>`. A law's closure is its direct IDs plus the closures of cited lemmas and alpha aliases. Profiles propagate through imported specs and bundle dependencies.

Reports and records expose `:assumptions-used`. Attestation reports a law whose closure grows or changes as weaker. Adding or changing an unused assumption is not weakening; global declarations alone no longer define what a proof relies on.

### Normalized lemma retrieval

`writ.reuse` indexes already proved lemmas using the same forall splitting, goal translation, binder renaming, and rewrite normalization as proof lemma rules. Exact normalized matches rank before related shapes. Candidates are deterministic and eligible only when their assumption closure is allowed.

Suggestion uses ranked lemma pools, then falls back to existing search and synthesis. A returned hint uses only lemmas actually cited by the successful checked proof. Retrieval never runs in ordinary proving and cannot make a candidate evidence.

## Alternatives considered

- **Trust semantic cache keys:** rejected because edited/corrupt caches can assert proof and contract rules can affect later proofs.
- **Bundle source files and rerun checks:** rejected because it reruns tests/search and loads project code instead of independently replaying evidence.
- **Port Rainbow's kernel:** rejected because its dependent mathematics and Writ's Clojure-code semantics differ.
- **Copy canonical encoding unchanged:** rejected after reproducing an unpaired-surrogate hash collision.

## Validation

Each task uses failing tests first. Focused suites run on jolt after each change; `bin/test` is the final gate. End-to-end validation covers cold/warm caches, law and contract tampering, fresh bundle verification, transitive assumption reporting, and deterministic retrieval. No commit or push occurs without explicit approval.
