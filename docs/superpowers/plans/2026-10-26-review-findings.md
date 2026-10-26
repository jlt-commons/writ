# Review Findings Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Fix all five correctness and performance findings under `writ-a24` and deliver them on one tested branch and PR.

**Architecture:** Add a single raw-form free-symbol traversal in `writ.lower`, then build substitution and qualification on it. Keep adequacy and CDCL changes local: isolate baseline evaluation from stand-in dispatch and use balanced, path-compressed union-find.

**Tech Stack:** Clojure on jolt, clojure.test, existing Writ proof/solver machinery, beads, GitHub CLI.

**Spec:** `docs/superpowers/specs/2026-10-26-review-findings-design.md`

## Global Constraints

- Use jolt and existing dependencies only; do not add Z3 or alter proof semantics.
- Every implementation change starts with a failing regression test.
- Do not reduce sample sizes, skip adequacy, or weaken the hanging test.
- Preserve deterministic solver component contents/order and parallel/sequential spec behavior.
- Leave pre-existing untracked `blog.md` and `.beads.gate.lock` untouched.
- Work on `fix/review-findings`; deliver one PR for `writ-a24` and its five children.
- Claim each child issue with `bd update <id> --claim` before its task's Step 1; close it only after that task's verification passes.

## Review Focus

- Sequential `let`/`loop` initializers: names remain free until their own binder is established; Task 1 tests this directly.
- Destructuring options: `:or` defaults and lookup keys are not binders, while nested patterns and `:as` aliases are; Task 1 tests all variants.
- Resolution precedence: qualification still resolves proof-own names before target publics and spec interns; Task 2 tests the order.
- Recursive stand-ins: only the baseline bypasses dispatch; the stand-in still recurses through the impostor; Task 3 tests a recursive impostor's actual result and the original typey scenario.
- Component determinism: union by rank and path compression must not reorder clauses within components or change smallest-first grouping; Task 4 tests exact output.

---

### Task 1: Shared Raw-Form Scope and Substitution

**Files:**
- Create: `test/writ/lower_test.clj`
- Modify: `test/writ/test_runner.clj`
- Modify: `src/writ/lower.clj:98-107`
- Modify: `src/writ/proposition.clj:8-27`
- Modify: `src/writ/spec.clj:3097-3117`
- Modify: `test/writ/bundle_test.clj`
- Modify: `docs/superpowers/specs/2026-10-26-review-findings-design.md` (already created)

**Interfaces:**
- Produces: `writ.lower/binding-names [bform]`, returning a vector of every binder and no markers/options.
- Produces: `writ.lower/transform-free [form bound f]`, rebuilding `form` with each currently free symbol `s` replaced by `(f s)`; `bound` is a set of symbols.
- Produces: `writ.lower/subst-var [form x e]`, the shared free-variable substitution used by proposition and spec code.

- [ ] **Step 1: Write failing binder and substitution tests**

Create `lower_test.clj` covering:
- `'{:keys [a] :as m :or {a 1}}` => `[a m]`;
- `'{x :x, [y] :ys, {:keys [z]} :nested}` => `[x y z]`;
- `'[a & xs :as all]` => `[a xs all]`;
- namespaced `:keys`/`:strs`/`:syms` bind their local symbols;
- `(transform-free '(let [x x, y x] [x y]) #{'x} f)` substitutes only the first initializer and leaves both body references bound;
- `fn` parameter/name shadowing, quote, and quantifier type/body scope;
- `(subst-var '(forall [x Nat] (let [x x] x)) 'x '_0)` replaces the initializer but not the shadowed body.

Add `writ.lower-test` to `test-namespaces`. In `bundle_test.clj`, assert that `proposition/alpha=` is true for `(forall [x Nat] (let [x x] x))` and `(forall [y Nat] (let [x y] x))`, and that substitution under `{:as x}` does not replace the bound reference.

- [ ] **Step 2: Run the tests and confirm the original defects**

Run: `jolt -M:test --run writ.lower-test writ.bundle-test`
Expected: new binder/scope assertions fail; existing assertions pass.

- [ ] **Step 3: Implement shared scope handling**

In `writ.lower`, make `binding-names` recursively collect actual binders from vector/map destructuring, skipping `&`, `:as` markers, `:or`, and lookup keys. Add `transform-free` with sequential `let`/`loop` environments, single-arity `fn` name/parameter environments, quantifier scope, quote handling, and collection preservation. Implement `subst-var` through it. Delegate both raw-form substitution copies to `writ.lower/subst-var` and remove the duplicate walkers.

- [ ] **Step 4: Run focused tests**

Run: `jolt -M:test --run writ.lower-test writ.bundle-test writ.gaps-test writ.graph-test`
Expected: all complete with zero failures/errors.

- [ ] **Step 5: Claim, commit, and close the completed child issues**

Claim `writ-n45` and `writ-zz8` before implementation, then commit the design document, plan, source, and tests with message `fix: preserve lexical scope in raw forms`. Close `writ-n45` and `writ-zz8` only after the focused tests pass.

### Task 2: Scope-Safe Law Qualification

**Files:**
- Modify: `src/writ/spec.clj:1496-1526`
- Modify: `test/writ/spec_test.clj`

**Interfaces:**
- Consumes: `writ.lower/transform-free [form bound f]` from Task 1.
- Produces: the existing private `writ.spec/qualify` arities and resolution behavior, without rewriting bound names.

- [ ] **Step 1: Write failing qualification tests**

Using the existing private `qualify` helper, assert:
- `'(let [f 1] (insert f))` with target publics `#{f insert}` becomes `'(let [f 1] (demo.target/insert f))`;
- `'((fn [insert] (insert 1)) f)` qualifies only free `f` and the local call remains `insert`;
- a shadowing binder's initializer still qualifies the outer target name;
- proof-own resolution wins over target publics, target publics win over spec interns, and namespaced aliases retain existing behavior.

- [ ] **Step 2: Run tests and confirm the original defect**

Run: `jolt -M:test --run writ.spec-test`
Expected: the new local-binder assertions fail with qualified binding positions/references.

- [ ] **Step 3: Implement qualification through `transform-free`**

Preserve both public arities and the existing resolution callback, including proof-own/target/spec precedence and alias handling. Pass the initial bound set and let the shared traversal manage binders.

- [ ] **Step 4: Run focused tests**

Run: `jolt -M:test --run writ.spec-test writ.prove-test`
Expected: all complete with zero failures/errors.

- [ ] **Step 5: Claim, commit, and close**

Claim `writ-0hm` before implementation. Commit with message `fix: respect local binders during qualification`. Close `writ-0hm` after tests pass.

### Task 3: Linear Baseline Evaluation During Adequacy

**Files:**
- Modify: `src/writ/spec.clj:2288-2304`
- Modify: `test/writ/starved_test.clj:237-244`

**Interfaces:**
- Produces: unchanged `survives?` behavior and impostor semantics; baseline calls evaluate with `writ.spec/*stand-ins*` bound to `{}`.

- [ ] **Step 1: Strengthen the failing regression test**

Change the typey adequacy test to run `writ.spec-demo.typey-spec` with both `{:parallel true}` and `{:parallel false}`, retaining the original seed and sample counts. Add a small direct recursive-impostor assertion proving the impostor still applies at recursive calls while the baseline uses original recursion.

- [ ] **Step 2: Reproduce the hang before the fix**

Run: `jolt -M:test --run writ.starved-test:3/4`
Expected: does not complete within 30 seconds at `a-law-that-rejects-no-stand-in-is-named`; stop the spawned process after recording the timeout.

- [ ] **Step 3: Isolate baseline evaluation**

At the comparison in `survives?`, call the original function inside `(binding [*stand-ins* {}] ...)`. Do not alter the stand-in call, `called`/`differed` accounting, generated samples, or impostor generation.

- [ ] **Step 4: Verify the original end-to-end scenario**

Run: `jolt -M:test --run writ.starved-test:3/4 writ.speed-test`
Expected: completes within the normal shard time with zero failures/errors, including both parallel modes.

- [ ] **Step 5: Claim, commit, and close**

Claim `writ-3je` before implementation. Commit with message `fix: avoid exponential adequacy comparison`. Close `writ-3je` after the original scenario passes.

### Task 4: Near-Linear CDCL Component Partitioning

**Files:**
- Modify: `src/writ/solve/cdcl.clj:473-487`
- Modify: `test/writ/solve_test.clj`

**Interfaces:**
- Produces: unchanged private `components [clauses]` output contract: clause order within components and components sorted by count.

- [ ] **Step 1: Write exact component tests and record the scaling baseline**

Test disconnected clauses, one connected chain, shared variables across inequality/boolean literals, and empty clauses. Assert exact grouped clauses and smallest-first ordering. Record five-run timings for fresh chain inputs at 400, 800, 1600, and 3200 variables using the existing private `components` function.

- [ ] **Step 2: Run correctness tests and baseline**

Run: `jolt -M:test --run writ.solve-test`
Expected: correctness assertions pass, while the timing record demonstrates the original superlinear growth.

- [ ] **Step 3: Implement balanced path-compressed union-find**

Use union by rank/size and path compression (iterative find or recursive find with parent compression). Compute each clause's root once for final grouping; preserve deterministic grouping and smallest-first ordering without changing literal numbering or search state.

- [ ] **Step 4: Run solver tests and repeat the timing record**

Run: `jolt -M:test --run writ.solve-test`
Expected: zero failures/errors and near-linear timing growth, with no regression in certificate/model checks.

- [ ] **Step 5: Claim, commit, and close**

Claim `writ-cxv` before implementation. Commit with message `perf: balance CDCL constraint union-find`. Close `writ-cxv` after tests and scaling verification pass.

### Task 5: Whole-Branch Verification and PR

**Files:**
- Modify only if verification exposes a regression in the tasks above.

**Interfaces:**
- Consumes all previous task deliverables.

- [ ] **Step 1: Review the complete diff**

Run: `git diff main...HEAD --check` and inspect `git diff main...HEAD --stat` plus the changed source/tests. Confirm no unrelated files or generated caches are included.

- [ ] **Step 2: Run the full standard suite**

Run: `bin/test`
Expected: the formerly hanging starved shard completes; final counters show zero failures/errors.

- [ ] **Step 3: Run the prover benchmark**

Run: `bin/bench --jobs 1 --baseline bench/baseline.edn`
Expected: no lost laws and no reported slowdowns. Record gained/faster rows as informational, not requirements.

- [ ] **Step 4: Close the epic and publish**

After all five children and gates are complete, close `writ-a24`. Commit any final verification changes, run `git pull --rebase origin main`, rerun focused tests if rebase changes the branch, push with `git push -u origin fix/review-findings`, and open a PR using `gh pr create`. The PR body summarizes the five fixes, links `writ-a24` and all children, and includes the exact full-test and benchmark results.
