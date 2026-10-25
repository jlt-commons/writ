# Replayable Proof Evidence Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make every cached Writ proof and contract freshly replayed, then add independently replayable proof bundles, per-law assumption closure, and untrusted normalized lemma retrieval.

**Architecture:** Keep `writ.prove.check` as the only proof authority. Ordinary checks may recover from invalid cached evidence by searching again; bundle verification has no search path and only replays self-contained prover inputs. Retrieval ranks existing proved lemmas but never changes what counts as proof.

**Tech Stack:** Clojure on jolt, existing Writ rewriter/prover/solver, clojure.test, test.check; no new dependencies.

**Spec:** `docs/superpowers/specs/2026-10-25-replayable-proof-evidence-design.md` (created from the approved review decisions with this plan); Beads epic `writ-4du` and tasks `.1`-`.5` are the tracking source.

## Global Constraints

- Run on jolt with the current `deps.edn`; add no libraries and no Z3.
- A cached result, derived rule, retrieval candidate, or report is never proof. Only fresh `writ.prove.check` replay establishes a cached or bundled proof.
- Ordinary `spec/check` may search again after rejected/missing evidence. Bundle verification must never search, execute project code, load specs, or rerun tests.
- Old cache files without traces are cache misses, not errors. Corrupt cache files retain the current best-effort recovery behavior.
- Assumed signatures and assumed laws remain explicit external trust. Bundles list them; they do not silently become proved facts.
- Preserve current public behavior except for the new evidence metadata/APIs and the deliberate attestation change: unused assumptions do not weaken a spec.
- Keep changes on `feature/replayable-proof-evidence`; do not modify Rainbow or the pre-existing untracked `blog.md`.
- Use Beads for task status. Do not commit or push without explicit user approval.
- Update README semantics in the task that changes them. Add new test namespaces to `writ.test-runner/test-namespaces`.

## Review Focus

- Legacy cache entries lack traces: recover by proof search and rewrite valid evidence (Tasks 1-2).
- A tampered trace has a recomputed bundle ID: replay still rejects it rather than trusting content addressing (Task 3).
- A law proved by an alpha-equivalent earlier law has no fresh trace: verify a checked alias reference (Task 3).
- Two used specs declare different assumptions with one short name: profiles stay namespace-qualified and cannot merge accidentally (Task 4).
- Retrieval has no eligible candidate or only assumption-backed candidates: suggestion falls back to its current search and does not broaden evidence policy (Task 5).
- Canonical data includes maps, sets, ratios, floats, keywords, symbols, and unpaired UTF-16 surrogates: encoding stays deterministic and injective (Task 3).

---

### Task 1: Replay cached law proofs — `writ-4du.1`

**Files:**
- Modify: `src/writ/spec.clj:5084-5535`
- Modify: `test/writ/proof_test.clj:90-169`
- Modify: `README.md:1263-1278`
- Create: `docs/superpowers/specs/2026-10-25-replayable-proof-evidence-design.md`
- Create: `docs/superpowers/plans/2026-10-25-replayable-proof-evidence.md`

**Interfaces:**
- Consumes: existing traces keyed by `law-id` and replay through `prover/prove-law` with `:replay`.
- Produces: on every cached success, a fresh `prove-law` result with `:replayed true`; `:cached true` means a semantic entry existed, never that replay was skipped.

- [ ] **Step 1: Record the design and this plan**
  Write the approved goals, non-goals, trust boundaries, bundle schema decisions, per-law assumption semantics, retrieval policy, and validation commands to the design doc. Copy this plan to its repository path.

- [ ] **Step 2: Add failing cache-tamper tests**
  In `a-cached-proof-is-replayed-and-a-wrong-one-never-proves`, keep the semantic results, run again, and assert every proved law has both `:cached` and `:replayed` and a successful `:replay` attempt. Add a case using `writ.spec-demo.sort-lemma-spec` with `:proof false`: cache a run, replace every cached law result with `{:proved true :summary "forged"}`, remove all traces, rerun, and assert `sorted` is not `:proved`.

- [ ] **Step 3: Run the tests and confirm the forged-success case fails**
  Run: `jolt -M:test --run writ.proof-test`
  Expected: the new forged-result case reports a forged proof under the current exact-hit shortcut; existing replay cases still run.

- [ ] **Step 4: Bypass cached success values and replay their traces**
  In `prove-laws`/`attempt`, use a cached result directly only when it is a failed-search result. For a cached success, call `attempt*` with the stored `law-id` trace and associate `:cached true` afterward. Missing or rejected traces follow the existing fresh-search path; failed-search caching stays unchanged.

- [ ] **Step 5: Update cache documentation and close the Beads task after verification**
  State that every successful cached law proof is replayed on every check. Run `jolt -M:test --run writ.proof-test`, expect PASS, inspect the diff, then mark `writ-4du.1` complete only after all new and old cases pass.

### Task 2: Replay cached function contracts — `writ-4du.2`

**Files:**
- Modify: `src/writ/prove.clj:1030-1126`
- Modify: `src/writ/spec.clj:5139-5159,5433-5444`
- Modify: `test/writ/prove_test.clj:434-472`
- Modify: `test/writ/proof_test.clj:90-169`
- Modify: `README.md:1274-1278`

**Interfaces:**
- Consumes: Task 1 replay-on-cache-hit behavior.
- Produces: `prover/prove-contracts` accepts `{:defs :tenv :sigs :fuel :traces :replay-only}` and returns `{:rules [...] :traces {contract-key trace} :replay-errors [...]}`. Contract keys remain `[f "%contract"]` / `[f "%nonneg%contract"]`.
- `cached-contracts` returns that full evidence map; law construction uses `:rules`, bundles later use `:traces`.

- [ ] **Step 1: Add failing contract replay tests**
  Extend the direct contract tests to capture the evidence map, assert the existing rule names under `:rules`, and assert a second run with its traces and `:replay-only true` returns the same rules without search. Corrupt every trace and assert replay-only returns no rules and nonempty `:replay-errors`. Add a spec-level case where forged cached `:rules` and missing traces are ignored and valid contracts are recomputed.

- [ ] **Step 2: Run focused tests and confirm the new API/replay assertions fail**
  Run: `jolt -M:test --run writ.prove-test writ.proof-test`
  Expected: current vector-only contract results and trusted cached rules cannot satisfy the new assertions.

- [ ] **Step 3: Persist and replay contract traces**
  In `prove-contracts`, keep the existing goal construction, dependency ordering, and fresh-proof search. For each contract, first try its supplied trace with `check/check-proof` against the regenerated goal and currently usable earlier rules. On success store the trace; on failure either search (ordinary check) or omit the rule and record the error (`:replay-only`). Return derived rules only from goals accepted in this run.

- [ ] **Step 4: Make cached rules untrusted**
  Change `cached-contracts` to pass cached traces to `prove-contracts`; never return cached `:rules` directly. Old entries without traces recompute. Save `:rules` for readability and `:traces` for subsequent replay. Adapt `prove-laws` to use `(:rules @contracts)`.

- [ ] **Step 5: Verify and update tracking/docs**
  Run the focused command until PASS, then `jolt -M:test --run writ.prove-test:1/3 writ.prove-test:2/3 writ.prove-test:3/3 writ.proof-test` if shard interaction needs checking. Document fresh contract replay and close `writ-4du.2`.

### Task 3: Add standalone proof bundles — `writ-4du.3`

**Files:**
- Create: `src/writ/canonical.clj`
- Create: `src/writ/proposition.clj`
- Create: `src/writ/bundle.clj`
- Create: `test/writ/bundle_test.clj`
- Modify: `src/writ/spec.clj` (evidence capture, `:bundle` option, alpha helper delegation)
- Modify: `src/writ/prove.clj` (explicit `:replay-only`)
- Modify: `test/writ/test_runner.clj:16-23`
- Modify: `README.md` (proof cache/records sections and a short bundle section)

**Interfaces:**
- Consumes: Task 2 `{:rules :traces :replay-errors}` contract evidence and fresh law replay.
- Produces:
  - `canonical/content-id value` -> SHA-256 string over deterministic, injective canonical data.
  - `proposition/alpha= p q` -> boolean; existing `spec/alpha=` delegates here.
  - `(spec/check 'my.spec {:bundle "proof.edn"})` writes a versioned bundle.
  - `(bundle/verify path-or-map)` -> `{:ok boolean :laws [...] :contracts n :assumptions [...] :error ...}`; no search or project loading.
  - `prover/prove-law` accepts `:replay-only true`; rejected/missing replay cannot enter search or counterexample search.

- [ ] **Step 1: Add failing canonical and bundle tests**
  Test deterministic IDs across reordered maps/sets and distinct IDs for `1` vs `"1"`, lists vs vectors, valid Unicode, and `(str (char 0xd800))` vs `"?"`. Export `writ.spec-demo.index-spec` with `:cache false`, verify the bundle, and assert all exported laws replay. Tamper a trace, recompute the outer ID to defeat the simple hash check, and assert rejection. Cover a synthetic alpha-alias entry, an unknown cited lemma, an altered contract trace, and malformed schema.

- [ ] **Step 2: Run the new tests and confirm the APIs are absent**
  Run: `jolt -M:test --run writ.bundle-test`
  Expected: FAIL to load because `writ.bundle`/canonical APIs and `:bundle` support do not exist.

- [ ] **Step 3: Implement canonical data and shared alpha equivalence**
  `writ.canonical` encodes values with explicit type tags, sorted map/set encodings, and strings as UTF-16 code-unit data before SHA-256 via `writ.hash`; support all literal values occurring in prover inputs. `writ.proposition` owns the existing capture-aware leading-`forall` alpha canonicalization moved from `spec`.

- [ ] **Step 4: Capture pure evidence during `prove-laws`**
  Add explicit replay-only behavior to `prove-law`. Return `{:results ... :evidence ...}` from `prove-laws` and adapt its single caller. For each proved law retain only EDN prover inputs (`:prop :defs :tenv :own :sigs :contracts :lemmas :rets :trusted-rets :component-requires :guards :hint :fuel :total :lemma`), its trace, and assumption metadata. Represent the existing alpha-shortcut as `{:kind :alias :of name}`. Collect dependency evidence from `imports-of`; never retain functions, delays, atoms, or runtime callbacks in a bundle.

- [ ] **Step 5: Implement bundle writing and replay-only verification**
  Define schema 1 with `:spec :target :sources :contracts :dependencies :laws :assumptions :runtime-evidence :id`; ID covers every other field. Verification recomputes ID, replays contract traces with `:replay-only`, rebuilds target and assumed-signature rules, verifies dependencies before dependents, and requires every cited lemma to match an earlier verified entry or an explicitly listed assumption. Replay each law with verified rules and its pure inputs; aliases require an earlier alpha-equivalent verified law. Runtime-only evaluated/witnessed claims are listed separately, never reported as replayed proofs.

- [ ] **Step 6: Wire `:bundle`, docs, and test runner**
  Validate the option string, write atomically with existing `spit-whole!`, and expose the verification namespace without creating a `writ.bundle` -> `writ.spec` dependency. Document that bundles verify included prover evidence and explicitly retain assumptions/runtime evidence boundaries.

- [ ] **Step 7: Verify end to end and close the task**
  Run `jolt -M:test --run writ.bundle-test writ.proof-test writ.prove-test`, expect PASS. Verify a real bundle in a fresh jolt invocation, then close `writ-4du.3`.

### Task 4: Report per-law assumption closure — `writ-4du.4`

**Files:**
- Modify: `src/writ/prove.clj:728-936`
- Modify: `src/writ/spec.clj` (profiles, records, attestation, bundle evidence)
- Modify: `src/writ/bundle.clj` (profile validation)
- Modify: `test/writ/assume_test.clj`
- Modify: `test/writ/domain_test.clj` (general attestation cases)
- Modify: `test/writ/bundle_test.clj`
- Modify: `README.md` (assumptions, records, report map)

**Interfaces:**
- Consumes: Task 3 verified law entries, dependency bundles, and explicit assumption list.
- Produces: each law result has `:assumptions-used`, a sorted vector of stable IDs: `assume.<qualified-fn>` for signatures and `assume.<spec-ns>/<law>` for assumed laws. Imported lemmas carry their transitive closure. Records store the same vector per law; attestation emits `:assumptions-added` / `:assumptions-changed` for a law whose closure grows or changes.

- [ ] **Step 1: Add failing profile and attestation tests**
  Extend `laws-that-rest-on-assumptions-are-proved`: assert cleaning laws include trim/lower-case laws actually cited, `a-string-has-its-own-slug` does not inherit unrelated declarations, and composed specs include the dependency's transitive profile. Add a record comparison where a law gains an assumption and is weaker, contrasted with `slug-unused-spec` where its unused `starts-with?` declaration may be added/changed without weakening. Add a bundle profile-tamper rejection.

- [ ] **Step 2: Run focused tests and confirm missing metadata/semantic failures**
  Run: `jolt -M:test --run writ.assume-test writ.domain-test writ.bundle-test`
  Expected: no per-law closure exists and global assumption comparison rejects unused additions.

- [ ] **Step 3: Capture direct assumption use in the checker replay**
  Give `prove-law` the mapping from assumed contract rule names to qualified fns and the set of assumed law names. From checker `:lemmas-used`, return direct signature/law IDs separately from ordinary `:lemmas`. Do not infer usage from source occurrences or from a summary string.

- [ ] **Step 4: Compute transitive, namespace-safe closure**
  Mark assumed lemmas with their own IDs and imported lemmas with their existing profiles. As each law/lemma is proved, union its direct IDs with the profiles of cited lemmas; alpha-alias laws inherit the referenced law's profile. Propagate profiles through `::proved-props`, bundle dependencies, report law entries, and `record-of`.

- [ ] **Step 5: Make attestation compare actual evidence**
  Compare each law's old/new assumption closure. Retain global checks for removed obligations and changed assumptions that are used. Allow an unused declaration to be added or changed, and update README wording from “every declared assumption” to the precise actual-dependency rule.

- [ ] **Step 6: Verify bundle profiles and documentation**
  Bundle verification derives each law's closure from replay and compares it with the exported profile. Run focused tests until PASS, inspect report text for readability, then close `writ-4du.4`.

### Task 5: Retrieve lemmas by normalized proposition — `writ-4du.5`

**Files:**
- Create: `src/writ/reuse.clj`
- Create: `test/writ/reuse_test.clj`
- Modify: `src/writ/spec.clj:5292-5339,5695-5724`
- Modify: `src/writ/proposition.clj` only if shared canonical binder helpers are needed
- Modify: `test/writ/test_runner.clj:16-23`
- Modify: `README.md:1414-1438`

**Interfaces:**
- Consumes: Task 4 proved lemma entries and `:assumptions-used` profiles; Task 3 pure definitions/type environments.
- Produces:
  - `(reuse/index lemmas {:defs ... :tenv ... :own ...})` -> immutable normalized proposition index.
  - `(reuse/candidates index prop {:allowed-assumptions #{...} :limit n})` -> deterministic eligible lemma entries, exact normalized matches first, then related shapes.
  - `suggest-proof` uses ranked lemma pools and includes the actually cited lemma names in a returned hint's `:use`; with no candidates it uses the current hint/lemma synthesis unchanged.

- [ ] **Step 1: Add failing retrieval tests**
  Index an alpha-variant and arithmetic-normalized pair such as `(forall [x Int] (= (+ x 0) x))` and `(forall [y Int] (= y (+ 0 y)))`; assert exact retrieval. Test deterministic related ranking, exclusion of entries marked unproved, rejection of assumption-backed candidates outside `:allowed-assumptions`, and empty-policy fallback. Add a suggestion test asserting the returned `:use` contains only lemmas cited by the successful proof.

- [ ] **Step 2: Run tests and confirm the namespace/integration are absent**
  Run: `jolt -M:test --run writ.reuse-test`
  Expected: FAIL to load `writ.reuse`.

- [ ] **Step 3: Implement normalized proposition indexing**
  Reuse the same `split-foralls`, `scheme/goal`, binder renaming, and `rw/normalize` path as `lemma-rules`, so keys reflect the prover's semantics rather than printed syntax. Store canonical binding types, normalized hypotheses/goals, assumption profiles, and stable names. Filter any entry explicitly marked unproved; the caller's available lemmas are otherwise already proof-checked.

- [ ] **Step 4: Implement deterministic, policy-aware candidates**
  Exact normalized keys rank first. Related candidates rank by shared normalized goal/head/constants, then assumption-free status and name. An entry is eligible only when its assumption closure is a subset of the allowed set; default to the empty set in the public API. Never call the prover from retrieval.

- [ ] **Step 5: Integrate ranked pools without narrowing ordinary proofs**
  Build the index once per suggestion, pass the spec's declared/ imported assumption closure as allowed, and try ranked pools before the full existing lemma set. On success use the proof result's actual `:lemmas` to emit a minimal `:use`. Do not change ordinary `prove-laws` search or accept a retrieved candidate without its normal checked proof.

- [ ] **Step 6: Verify and close the epic task**
  Run `jolt -M:test --run writ.reuse-test writ.proof-test writ.assume-test`, expect PASS. Document that retrieval is untrusted and assumption-policy preserving. Close `writ-4du.5` only after the full-suite gate below also passes.

### Final whole-branch verification and handoff

- [ ] Run `bin/test`; require zero failures and zero errors.
- [ ] Run a fresh end-to-end scenario: cold cache, warm cache, tampered law trace, tampered contract trace, exported bundle verification, and assumption-profile report on an existing real spec.
- [ ] Review `git diff --check`, `git status`, README consistency, public return shapes, and Beads acceptance criteria. Do not claim the hours-long external Rainbow suite or any unrun Writ scenario.
- [ ] Report changed files, test evidence, remaining risks, and branch status. Ask before committing or pushing; leave `blog.md` untouched.
