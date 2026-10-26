# Review Findings Design

## Intent and why

The 2026-10-26 review found three related lexical-scope defects, one exponential adequacy path, and one quadratic solver path. The adequacy defect prevents the standard test suite from completing. This project fixes all five under epic `writ-a24`, on `fix/review-findings`, with regression tests that demonstrate each original failure before the corresponding fix.

## Goals

1. Make adequacy comparison linear in the target function's own recursive evaluation rather than recursively evaluating both versions.
2. Preserve local lexical bindings when qualifying target and spec names in laws and contracts.
3. Return every actual binder from `binding-names`, without returning binding markers or option data.
4. Substitute exactly the free occurrences in raw propositions, including sequential binding initializers, and use the same scope rules in proposition and spec code.
5. Partition CDCL constraint components in near-linear time while preserving deterministic component contents and ordering.
6. Make `bin/test` complete and pass, and rerun the prover benchmark against its saved baseline.

## Non-goals and anti-goals

- Do not refactor the proof AST, solver algorithm, adequacy model, or public specification syntax beyond these fixes.
- Do not change which impostors are generated or what adequacy means.
- Do not add dependencies, Z3, new caching semantics, or a second lexical-scope implementation.
- Do not silence the hanging test by reducing its sample sizes or skipping adequacy.
- Do not modify the pre-existing untracked `blog.md` or `.beads.gate.lock`.

## Constraints

Use jolt and the existing project dependencies and test conventions. Each fix needs focused failing tests first. Existing proof replay, certificate verification, deterministic generation, and parallel/sequential equivalence must retain their behavior. Work stays on `fix/review-findings`; the PR covers all five findings.

## Approaches

- **Chosen: shared raw-form scope handling plus targeted performance fixes.** One lexical traversal supplies substitution and qualification, while `binding-names`, adequacy baseline evaluation, and union-find receive local fixes. This directly removes the duplicated scope logic responsible for three findings without changing the proof AST.
- **Independent local patches:** smaller initial edits, but rejected because the two existing substitution copies could diverge again.
- **Lower raw forms and operate on the proof AST:** rejected as a broad refactor with unnecessary proof-semantics risk.

## Design

### Shared lexical scope

Extend `writ.lower/binding-names` to handle vector and map destructuring completely: ordinary symbols, nested patterns, rest binders, `:as`, `:keys`, `:strs`, `:syms`, explicit map entries, and namespaced variants. Exclude `&`, `:as` markers, `:or`, default expressions, and lookup keys. Preserve deterministic binding order.

Add one raw-form scope traversal in `writ.lower` for substitution and free-name qualification. It must handle quote, `let`/`let*`, `loop`/`loop*`, `fn`/`fn*`, `forall`, and `exists`. Sequential binding initializers use the environment before their own binder; bodies use all preceding binders. Function parameters and optional function names shadow in their bodies. Quantifier types remain outside the binder's scope. Existing single-arity restrictions remain unchanged.

`writ.proposition/subst-var` and `writ.spec/subst-var` delegate to the shared substitution operation. `writ.spec/qualify` uses the shared traversal with an environment and a callback that qualifies only currently free symbols. It must not qualify binding positions. Existing resolution precedence—proof-own definitions, target publics, spec interns, aliases, and core names—stays unchanged.

### Adequacy evaluation

When `survives?` computes the baseline result for comparison, evaluate the original function with `*stand-ins*` bound to `{}`. Recursive self-calls in that baseline therefore remain on the original function rather than re-entering the wrapper. The stand-in itself still dispatches recursively as intended, and difference detection remains unchanged. Verify the original typey check completes without reducing its sample sizes, in both parallel and sequential modes.

### CDCL components

Replace recursive, unbalanced union-find in `writ.solve.cdcl/components` with path-compressing find and union by rank or size. Persistent maps are acceptable at this preprocessing boundary; avoid mutating shared input. Preserve clause order within each component and smallest-component-first ordering. Add a chain-shaped scaling check that is generous enough not to be machine-fragile, plus exact component-content checks.

## Validation

Add regression coverage to the existing test namespaces for:

- recursive adequacy with the original `typey-spec` scenario and parallel/sequential checks;
- local `let` and `fn` names that shadow target/spec names, including free names in sequential initializers;
- all supported destructuring binder shapes and raw substitution under `:as` aliases;
- alpha-equivalence with shadowing `let` initializers and graph substitution equivalents;
- exact CDCL component partitioning and a large chain benchmark/guard.

Run focused suites after each fix, then `bin/test` to completion and `bin/bench --jobs 1 --baseline bench/baseline.edn`. No law losses or new benchmark slowdowns are acceptable. Commit the design, implementation, and tests on the fix branch, push it, and open one GitHub PR linked to `writ-a24` and the five child issues.
