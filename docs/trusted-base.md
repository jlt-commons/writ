# What you have to trust

A Writ proof is only as trustworthy as the semantics and checkers that give it
meaning. This page names that boundary. `docs/trusted-base.edn` pins the
corresponding source files by SHA-256, and `writ.trusted-base-test` fails when a
listed file changes without a deliberate manifest update.

The hashes make trusted-code changes visible. They do not prove that the code is
sound, and they are not evidence that a law holds.

## Semantic and replay code

The manifest covers these parts of an end-to-end code claim:

- **Source and specification semantics:** lowering, static purity and
  termination rules, types and data, quantities, annotations, matching, and the
  specification/proposition forms in `writ.spec` and `writ.proposition`.
- **Proof meaning and replay:** `writ.prove` and its term, translation, rewrite,
  induction-scheme, symbolic-evaluation, SMT, and replay namespaces. The search
  heuristics are untrusted, but the semantics they share with replay are not.
- **Solver verification:** `writ.solve`, `writ.solve.pre`, and
  `writ.solve.cert`. CDCL, simplex, case search, clause learning, and other
  certificate producers are untrusted; a bad producer must yield a rejected
  certificate, not an accepted false result.
- **Portable evidence:** `writ.bundle`, `writ.canonical`, and `writ.hash`.
  Bundle decoding and content identity are checked, but replay remains the
  evidence. Retrieval, cache metadata, benchmarks, and content IDs by themselves
  are not trusted evidence.

Pinning a namespace means any change there gets an explicit trust review, even
when the changed function is an untrusted search helper sharing the file.

## Below Writ

Writ also trusts jolt, its Clojure reader and runtime semantics, integer and
collection behavior, and the platform on which jolt runs. Tests, generators,
runtime instrumentation, and sampled counterexamples provide separate evidence;
they never become a proof link merely by increasing coverage.

A proof also rests on the assumptions named by its `:assumptions-used` closure.
Those assumptions are explicit external trust, not silently upgraded facts.
Closed evaluation and witnessed values are runtime evidence and are labelled
separately in proof bundles.

## Changing the trusted base

Review the semantic effect of the change, run the proof and solver certificate
tests, and update the affected hashes in `docs/trusted-base.edn` in the same
change. Do not update a hash merely to make the suite pass: the updated manifest
is the record that the trusted change was intentional.
