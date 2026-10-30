# Verification milestone

Implement a reproducible verification command after M4 Strings/Chars.

1. Give each run private GHC, manifest, JSON, and Lean build artifacts. Keep the
   existing `transpile.sh source [output]` interface for exporting Lean.
2. Add conservative semantic checks to the transpiler for machine numbers,
   partial operations modeled with defaults, and potentially infinite stepped
   enumeration. Keep explicit approximate-model exploration available. Neither
   policy is a certificate of translation correctness.
3. Audit Lean theorem dependencies and report model proofs, trusted SMT results,
   admissions, errors, missing properties, and timeouts through a JSON CLI.
   Success requires a completed process and a result for every annotation block.
4. Classify regression fixtures explicitly, including the M4 refusal examples;
   make CI build the unit-test target and run positive and negative fixtures.

Validation: existing Lean tests; Python orchestration/result-policy tests;
isolated end-to-end checks of true/false/admitted/empty properties, the two audit
counterexamples, Strings/Chars, and local imports; complete tracked-fixture run.

The paper track uses these artifacts as the start of a reproducible experimental
protocol. The typed IR/dictionary redesign, real Cabal project integration,
termination proof generation, and IDE migration to the result protocol remain
subsequent milestones. Existing uncommitted editor/example work is preserved.

## Completed validation

- `lake build GhcCoreToLean ghccoretolean`: passed, including existing M4 guards
  and the new conservative-policy guards (207 reported jobs, with cached work).
- Python result-policy and orchestration tests: 10 passed.
- Classified end-to-end corpus: 56/56 passed with two concurrent workers. This
  includes 41 tracked examples and 15 verification cases, counting the explicit
  SMT-trust policy variant separately. Expected failures remain failures from
  the verifier's perspective; the regression runner checks their classifications.
- Unmodified pinned Blaster: rebuilt its changed dependency closure in a
  temporary repository snapshot; 15/15 verifier cases and CharOps passed there.
  Existing dependency/build caches were reused. This was not a fresh container
  or an independent installation of the entire toolchain.
- Legacy export of StringBasics to a path containing spaces: generated output
  elaborated successfully.
- Extension TypeScript compilation, SIGTERM cancellation, whole-run timeout,
  and `git diff --check`: passed.

Local machine-readable evidence is retained in
`.lake/verification-results.json`, `.lake/verification-clean-results.json`, and
`.lake/verification-clean-char-results.json`. CI now emits the same full-corpus
report as an artifact. No remote CI run or deployment was performed.

The ordinary local dependency checkout still contains its pre-existing solver
path patch. It was not changed; the separate upstream-dependency run confirms
that the new verifier does not depend on that patch for the tested cases.
