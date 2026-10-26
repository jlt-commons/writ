# Rainbow Proof Engineering Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add observable lemma-reuse diagnostics, measured held-out reuse evaluation, and a pinned trusted-base inventory, then make shared schema-2 proof bundles the sole new export format if they pass the approved size and replay-overhead gate.

**Architecture:** Preserve Writ's existing proof and bundle semantics. Extend the suggestion-only reuse path and existing bench entry points, pin trusted sources with tested hashes, and decode any shared bundle back to the existing schema-1 artifact before replay.

**Tech Stack:** Clojure on jolt, clojure.test, test.check, Beads, existing Writ proof/bundle APIs and benchmark scripts.

**Spec:** `docs/superpowers/specs/2026-10-26-rainbow-proof-engineering-design.md`

## Global Constraints

- Work on `feature/rainbow-proof-engineering`; leave pre-existing untracked `blog.md` and `.beads.gate.lock` untouched.
- Use Beads for task tracking under epic `writ-ajr`; write failing focused tests before implementation.
- Add no dependencies and do not adopt Rainbow's kernel, binary bundles, lifecycle system, or mathematical corpus.
- Ordinary proving and lemma eligibility remain unchanged; ranked reuse stays suggestion-only and candidates still require checked proofs.
- Schema-1 verification remains compatible; if accepted, schema 2 becomes the sole new export format after demonstrating at least 50% total byte reduction, less than 10% per-bundle verification slowdown, and identical successful replay.
- Do not claim benchmark timing as correctness evidence. All proof and tamper tests must pass independently of benchmarks.

## Review Focus

- A malformed shared node graph can contain forward references, cycles, unknown tags, or duplicate roots: reject it before replay (Task 4 malformed-input tests).
- Disabling retrieval must not disable other suggestion strategies or reset their budget differently (Task 2 fallback tests).
- One unnormalizable lemma must not hide other lemmas or make diagnostics nondeterministic (Task 1 mixed-index tests).
- Adding schema 2 must preserve schema-1 verification while making all new exports schema 2, with no parallel output option (Task 4 compatibility tests).
- A trusted-source edit must fail the manifest test, while the documentation must not present the hash as a soundness proof (Task 3 drift test and documentation review).

---

### Task 1: Reuse Quarantine Diagnostics

**Files:**
- Modify: `src/writ/reuse.clj`
- Modify: `src/writ/spec.clj:5278-5325,5744-5779,7137-7159`
- Test: `test/writ/reuse_test.clj`

**Interfaces:**
- Produces: `(reuse/index lemmas context)` returns existing `:context` and `:entries`, plus `:quarantined [{:name symbol :reason :normalization-failed :message string}]`.
- Consumes: existing `(reuse/candidates index prop {:allowed-assumptions ... :limit ...})` remains unchanged.
- Produces: `spec/check` with `:suggest` adds `:reuse {:indexed n :lookups n :candidates n :quarantined [...]}`; each `:suggestion` may carry `:reuse-candidates n`.
- Produces: `{:suggest {:reuse false}}` disables only ranked retrieval.

- [ ] **Step 1: Write failing reuse-index and report tests**

Add a test with one normalizable lemma and one lemma whose normalization is forced to fail. Assert deterministic quarantine records sorted by name, the valid lemma remains eligible, and disallowed assumptions remain excluded. Add a suggestion check asserting the new `:reuse` summary and quarantine text, and a `{:suggest {:reuse false}}` check proving non-retrieval hints still run.

- [ ] **Step 2: Run the focused tests and verify failure**

Run: `jolt -M:test --run writ.reuse-test`
Expected: FAIL because `:quarantined`, the report summary, and `:reuse false` are absent.

- [ ] **Step 3: Implement deterministic quarantine and one index per suggestion run**

In `writ.reuse`, retain normalization error information instead of silently dropping it; sort both entries and quarantine. In `writ.spec`, build at most one reuse index from the final lemma set, pass it through suggestion options, aggregate lookup/candidate counts, and expose quarantine diagnostics only when suggestions are requested. Do not alter `reuse/candidates` eligibility or ordinary proving.

- [ ] **Step 4: Run focused tests and existing suggestion/proof tests**

Run: `jolt -M:test --run writ.reuse-test writ.proof-test`
Expected: PASS with no suggestion regressions.

- [ ] **Step 5: Document and commit**

Document `:reuse` diagnostics and `{:suggest {:reuse false}}` in `README.md`, then commit `src/writ/reuse.clj`, `src/writ/spec.clj`, `test/writ/reuse_test.clj`, and `README.md` with `feat: expose lemma reuse quarantine diagnostics`.

### Task 2: Held-Out Reuse Benchmark

**Files:**
- Modify: `src/writ/bench.clj:114-276`
- Modify: `bin/bench`
- Test: `test/writ/bench_test.clj`
- Modify: `README.md`

**Interfaces:**
- Consumes: Task 1's `{:suggest {:reuse boolean}}` and per-suggestion `:reuse-candidates`.
- Produces: `(bench/reuse-comparison tune-specs held-out-specs opts)` returns `{:tune corpus :held-out corpus}`; each corpus contains baseline/reuse rows and summaries, `compare`, citation frequencies, candidate totals, and quarantine records.
- Produces: `(bench/reuse-report result)` returns deterministic text; CLI `jolt -M:bench --reuse TUNE --held-out HELD_OUT` runs it.

- [ ] **Step 1: Write failing benchmark tests**

Use small existing specs and `{:jobs 1}`. Assert both corpora and both arms run, their spec/law key sets and suggestion budgets match, citation counts come only from successful suggestions' actual `:use` lists, quarantine records are propagated, and the report includes gained/lost proofs and held-out results. Include a fallback case proving `:reuse false` does not disable other hint strategies.

- [ ] **Step 2: Run the benchmark tests and verify failure**

Run: `jolt -M:test --run writ.bench-test`
Expected: FAIL because `reuse-comparison` and `reuse-report` do not exist.

- [ ] **Step 3: Implement the equal-budget comparison and CLI**

Derive both arms from one options map with cache and adequacy disabled and identical seed, prover, suggestion budget, and jobs. Only the nested suggestion `:reuse` flag differs. Reuse `bench/run`, `summary`, and `compare`; aggregate citations from returned checked suggestions, not offered pools. Add `--reuse` using the existing `--held-out` split and keep `--tune` behavior unchanged.

- [ ] **Step 4: Run focused tests and a real comparison**

Run: `jolt -M:test --run writ.bench-test writ.reuse-test`
Expected: PASS.

Run: `jolt -M:bench --jobs 1 --reuse test/writ/spec_demo --held-out examples/test`
Expected: both tuning and held-out reports complete with identical law key sets; save the reported output for the PR. If the examples require their own classpath, run the equivalent held-out namespaces from `examples` with `jolt -M:bench` there and record the exact command.

- [ ] **Step 5: Document and commit**

Document the new mode and held-out tuning rule in `README.md` and the `bin/bench` comment. Commit the four files with `feat: benchmark ranked lemma reuse on held-out specs`.

### Task 3: Trusted-Base Inventory and Hash Gate

**Files:**
- Create: `docs/trusted-base.md`
- Create: `docs/trusted-base.edn`
- Create: `test/writ/trusted_base_test.clj`
- Modify: `test/writ/test_runner.clj:16-23`
- Modify: `README.md`

**Interfaces:**
- Produces: `docs/trusted-base.edn` as `{:version 1 :files [{:path string :sha256 string} ...]}` sorted by path.
- Consumes: existing `(writ.hash/sha256 string)` and `clojure.java.io/file`.

- [ ] **Step 1: Write the failing manifest test**

Read the EDN manifest and assert version 1, unique sorted paths, existing files, and exact current SHA-256 hashes. Include a pure mismatch assertion showing changed content is rejected. Register `writ.trusted-base-test` in the standard runner.

- [ ] **Step 2: Run the test and verify failure**

Run: `jolt -M:test --run writ.trusted-base-test`
Expected: FAIL because the manifest does not exist.

- [ ] **Step 3: Write the inventory and initial hashes**

Document the end-to-end semantic/replay trust boundary and external jolt/runtime trust. List lowering/static semantics, proposition translation, rewrite/induction, proof replay, symbolic/SMT translation, `writ.solve`, `writ.solve.pre`, `writ.solve.cert`, and bundle/canonical/hash code; explicitly exclude solver search as an untrusted producer. State that hashes detect change, not unsoundness. Compute the initial hashes from the listed files.

- [ ] **Step 4: Run the trusted-base and adjacent replay tests**

Run: `jolt -M:test --run writ.trusted-base-test writ.contract-replay-test writ.bundle-test`
Expected: PASS.

- [ ] **Step 5: Link the documentation and commit**

Link the inventory from `README.md`'s proof-checking discussion and explain the required manifest update on trusted edits. Commit all Task 3 files with `docs: pin and explain the trusted base`.

### Task 4: Measure and Conditionally Add Shared Bundles

**Files:**
- Modify: `src/writ/bundle.clj`
- Modify: `src/writ/canonical.clj` only if shared node encoding belongs there rather than the bundle codec
- Modify: `src/writ/spec.clj` only if the gate passes
- Create: `src/writ/bundle_bench.clj` for reproducible real-export measurement; remove it if the gate fails
- Create: `bench/bundle-baseline.edn`
- Test: `test/writ/bundle_test.clj`
- Modify: `README.md`

**Interfaces:**
- Candidate: `(bundle/share schema-1-artifact)` returns a schema-2 shared EDN envelope; `(bundle/unshared envelope)` reconstructs the exact schema-1 artifact.
- Candidate: `(bundle/verify path-or-map)` dispatches schema 1 or decoded schema 2, then uses the same replay-only verifier.
- If accepted: `spec/check :bundle` writes schema 2 by default, with no format option; schema 1 remains verification-only.
- Measurement: `(writ.bundle-bench/measure specs iterations)` reports per-spec bytes, median read/decode/verify milliseconds, replay status, and gate totals.

- [ ] **Step 1: Write candidate codec and compatibility tests**

Test structural sharing of repeated terms, exact round trips for every supported literal and collection type, independent replay, dependencies, and recomputed-ID tampering. Add malformed cases for unknown tags, forward/out-of-range references, cycles, duplicate roots, and malformed nodes. During candidate measurement, assert the existing plain export remains schema 1.

- [ ] **Step 2: Run the candidate tests and verify failure**

Run: `jolt -M:test --run writ.bundle-test`
Expected: FAIL because shared encoding does not exist.

- [ ] **Step 3: Implement the candidate shared codec without changing the default yet**

Encode distinct canonical nodes once in a positional table with children restricted to earlier positions. Decode to the original schema-1 artifact and route it through existing verification; reject malformed graphs before replay. Keep `:bundle` output plain during measurement. Add the real-export measurement runner for `sort-proved-spec`, `tree-spec`, `index-spec`, `cells-spec`, and composed `shop-spec`, with fixed seeds, cache off, serial verification, warm-up, and at least five measured iterations.

- [ ] **Step 4: Run codec tests and measure the gate**

Run: `jolt -M:test --run writ.bundle-test`
Expected: candidate tests PASS.

Run: `jolt -cp src:test -m writ.bundle-bench bench/bundle-baseline.edn`
Expected: every plain and decoded-shared bundle replays successfully. Record per-bundle and total bytes plus median verification times in `bench/bundle-baseline.edn`.

Decision: proceed only if total shared bytes are at most 50% of plain bytes and every shared end-to-end verification median is less than 110% of its plain median. If not, remove the candidate codec, runner, and candidate-only tests; keep the measurements and document the rejected schema 2, then commit the negative result with `bench: measure shared proof bundle encoding` and skip the remaining steps.

- [ ] **Step 5: If accepted, make schema 2 the sole new export and complete compatibility tests**

Change `:bundle` to write schema 2, add public conversion helpers and schema-dispatching verification, and retain schema-1 verification without adding an output option. Update the earlier export assertions to require schema 2. Run `jolt -M:test --run writ.bundle-test writ.assumption-profile-test`; expect PASS. Document the default format, conversion, measured result, and compatibility guarantee in `README.md`.

- [ ] **Step 6: Commit the accepted result**

Commit the codec, measurement runner/results, tests, default export change, and documentation with `feat: make shared proof bundles the default`.

### Task 5: Full Verification, Beads, and Pull Request

**Files:**
- Review all changed files and `docs/superpowers/specs/2026-10-26-rainbow-proof-engineering-design.md`
- Review this plan and measurement output

**Interfaces:**
- Consumes: all previous task interfaces and their acceptance evidence.
- Produces: pushed `feature/rainbow-proof-engineering` and one GitHub PR linked to `writ-ajr`.

- [ ] **Step 1: Commit the approved design and plan if not already committed**

Commit only the two design/plan documents with `docs: design Rainbow proof engineering improvements`; do not include untracked user files.

- [ ] **Step 2: Run standard quality gates**

Run: `bin/test`
Expected: all tests and assertions pass, including the new trusted-base test.

Run: `bin/bench --jobs 1 --baseline bench/baseline.edn`
Expected: no lost laws; investigate unexpected regressions rather than editing the baseline.

Run: `git diff --check`
Expected: no whitespace errors.

- [ ] **Step 3: Verify the original scenarios end to end**

Confirm quarantine diagnostics appear on a deliberate normalization failure, the reuse benchmark compares identical workloads, a trusted-file content change is caught by its test, and every exported bundle in the measurement replays. If schema 2 shipped, verify a plain bundle, a converted shared bundle, and a tampered shared bundle from disk.

- [ ] **Step 4: Review and update Beads**

Run `bd preflight`, close each fully verified child issue with its evidence, and close `writ-ajr` only after all gates and measurements pass. Record a rejected shared encoding as the completed measurement outcome, not as shipped functionality.

- [ ] **Step 5: Push and open the PR**

Run `git status --short --branch`, ensure only intended files are committed, push `feature/rainbow-proof-engineering`, and open a PR to `main` with `gh pr create`. Include the epic ID, implementation summary, test/benchmark evidence, trusted-base implications, and the shared-bundle measurements and gate decision. Confirm the PR URL and final branch status.
