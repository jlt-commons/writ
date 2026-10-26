# Rainbow Proof Engineering Design

## Intent and why

The Rainbow comparison found four applicable proof-engineering practices that do not require adopting Rainbow's dependent-type kernel: visible reuse-index omissions, measured held-out retrieval evaluation, an explicit trusted-base inventory, and compact shared proof bundles. This project implements the first three under epic `writ-ajr`, measures the fourth on real Writ evidence, and implements it only if the agreed benefit gate passes. Work stays on `feature/rainbow-proof-engineering` and ends in one pull request.

## Goals

1. Make lemmas omitted from reuse indexing because normalization failed visible and deterministic, without changing candidate eligibility or ordinary proof search.
2. Add an equal-workload, equal-budget benchmark for ranked lemma reuse on tuning and held-out spec corpora, including actual lemma citations and quarantine counts.
3. Publish a precise trusted-base inventory and a test that makes changes to trusted files deliberate.
4. Measure schema-1 and candidate shared schema-2 bundles from real passing specs. Adopt shared EDN only when total serialized size falls by at least 50% and per-bundle end-to-end verification is less than 10% slower, with identical successful replay.
5. Preserve schema-1 verification for existing artifacts and all existing proof semantics. If schema 2 passes, make it the only format written by new `:bundle` exports.

## Non-goals and anti-goals

- Do not adopt Rainbow's kernel, proof terms, universe system, binary bundle encoding, lifecycle system, or mathematical corpus.
- Do not make retrieval, quarantine metadata, content IDs, benchmark results, or cached reports trusted evidence.
- Do not change which lemmas are eligible, allow additional assumptions, or run ranked reuse during ordinary proving.
- Do not add dependencies, Z3, a second proof semantics, or automatic quarantine/ranking based on benchmark popularity.
- Do not remove schema-1 verification or add a persistent plain/shared output option. Schema 2 becomes the sole new export format only after it passes the gate.
- Do not modify the pre-existing untracked `blog.md` or `.beads.gate.lock`.

## Constraints

Use jolt, the existing dependencies, Beads, and current test and benchmark conventions. Each implementation change starts with focused failing tests. Retrieval remains suggestion-only and every candidate still requires a checked proof. Bundle decoding is untrusted: malformed references are rejected and decoded evidence passes the existing replay-only verifier. The user approved one conditional epic and the bundle gate above, then chose schema 2 as the default new export format if accepted; if the gate fails, remove the experimental encoder and record the negative result rather than shipping it.

## Approaches

- **Chosen: one conditional epic with backward-compatible reading and a clean default.** Implement diagnostics, benchmarking, and the trusted-base inventory; measure a candidate shared encoding; if it passes, export only schema 2 while continuing to verify schema 1. This covers the requested investigation without maintaining two output paths.
- **Split bundle work into a later epic:** narrower initial PR, but rejected because the user explicitly requested the measurement and conditional port in this branch and PR.
- **Adopt Rainbow's full bundle and reuse machinery:** rejected as incompatible scope and unnecessary trusted-base churn.

## Design

### Reuse quarantine diagnostics

Change `writ.reuse/index` to retain its existing `:context` and `:entries` keys and add `:quarantined`. Each failed normalization produces a deterministic entry containing the lemma name, `:reason :normalization-failed`, and a useful error message. Entries and quarantine records are sorted by name. Existing normalization failures remain non-fatal and never become candidates.

Build the reuse index once per suggestion run rather than once per stuck law. `suggest-proof` receives the index and records bounded per-law candidate counts without exposing unbounded internal data. When `:suggest` is enabled, the check report includes `:reuse` with indexed and quarantined counts and the quarantine records; the text report names quarantined lemmas. `{:suggest {:reuse false}}` disables ranked retrieval for the benchmark while leaving all other suggestion strategies enabled. The default remains reuse enabled.

### Held-out reuse benchmark

Extend `writ.bench` with a reuse comparison over separate tuning and held-out namespace sets. Both arms run the same specs with the same seed, suggestion budget, prover configuration, parallelism, disabled cache, and disabled adequacy. The baseline uses `{:suggest {:reuse false}}`; the candidate uses the same options with reuse enabled. The existing law-row comparison reports gained and lost proofs and timing changes. Additional summaries report retrieval candidate use, lemmas actually cited by successful checked suggestions, and quarantined lemmas.

Add a `--reuse` bench mode using the existing `--held-out` split convention. Document that the held-out corpus must not be used to tune ranking. This project measures and reports the mechanism; it does not change ranking weights unless the measurements reveal a correctness defect.

### Trusted-base inventory and change gate

Add `docs/trusted-base.md` distinguishing the end-to-end code-claim trust boundary from external assumptions and untrusted search. Inventory the actual replay and semantic path: source lowering/static semantics, proposition translation, rewrite and induction rules, proof replay, symbolic/SMT translation, solver formula rebuilding and certificate checking, and bundle decoding/canonical identity. Include `writ.solve`, `writ.solve.pre`, and `writ.solve.cert`, but exclude CDCL/simplex search as untrusted producers. Name jolt and its runtime semantics as external trust; tests and runtime sampling remain separate evidence, never proof links.

Add a machine-readable `docs/trusted-base.edn` containing the trusted source paths and their SHA-256 hashes. A `writ.trusted-base-test` verifies that every listed file exists, every hash matches, and the documentation refers to the manifest. Any trusted-file edit therefore requires an explicit manifest update in the same change. The gate pins content, not line count; it does not claim that hashing establishes soundness.

### Bundle measurement and conditional schema 2

Export real schema-1 bundles with cache off and fixed seeds from passing proof-heavy specs, including `sort-proved-spec`, `tree-spec`, `index-spec`, `cells-spec`, and composed `shop-spec`. Record byte sizes and successful verification. Use the same candidate encoder for measurement and any shipped schema 2.

The candidate encoding stores each distinct canonical node once in a positional table, with children referring only to earlier positions. Preserve all existing literal types and collection distinctions. A schema-2 envelope carries the shared payload and schema version. Decoding reconstructs the exact schema-1 artifact, including its original content ID; the existing verifier then recomputes identity and replays every contract and law. Reject unknown tags, forward/out-of-range references, malformed nodes, cycles, and trailing or duplicate structural data rather than silently repairing them.

Measure UTF-8 bytes on disk and end-to-end read/decode/verify time after a warm-up, using repeated runs and medians on an otherwise comparable serial workload. Record results under `bench/bundle-baseline.edn` and summarize them in the PR. The gate is at least 50% reduction in total bytes across the corpus, less than 10% verification slowdown for each bundle, and identical successful replay. If any part fails, do not ship schema 2.

If accepted, `spec/check :bundle` writes schema 2 by default, with no plain/shared format option. `writ.bundle/verify` accepts either schema so existing schema-1 artifacts remain valid, but there is no new schema-1 output path. Public conversion helpers support plain-to-shared and shared-to-plain round trips for compatibility and measurement. No binary format is added.

## Validation

Add focused coverage for:

- deterministic quarantine records, continued indexing of normalizable lemmas, unchanged assumption policy, and `:reuse false` fallback;
- equal-options reuse comparison, held-out reporting, and actual-citation accounting;
- trusted manifest acceptance and detection of a changed trusted file;
- shared/plain round trips, schema-1 compatibility, malformed shared encodings, recomputed-ID tampering, dependencies, and independent replay if the size gate passes.

Run focused suites after each task, then `bin/test`, the existing `bin/bench --jobs 1 --baseline bench/baseline.edn`, the new reuse benchmark, and the real bundle export/verify measurement. Do not accept law losses or use benchmark timing noise as a correctness result. Commit the approved design, implementation, tests, measurements, and documentation; close completed Beads children and the epic; push the branch and open one PR linked to `writ-ajr`.
