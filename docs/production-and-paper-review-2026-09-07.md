# Production and paper review — 2026-09-07

The project is a substantial verification prototype with a useful developer workflow. It is not yet a dependable verifier of Haskell behavior. The first production milestone should establish what a successful verification means, and enforce that contract. Expanding the supported syntax before doing this increases the surface on which a translation can silently change a program.

Review baseline: HEAD `5ce6e1e`, plus the existing working tree. The VS Code findings below include uncommitted changes. The installed Blaster dependency also has a pre-existing local modification in `Blaster/Smt/Env.lean`; local build results are not evidence of clean-checkout reproducibility. No implementation fixes were made during this review.

**What is worth keeping.**

- Using GHC's desugared Core avoids implementing Haskell parsing, type checking, and desugaring in the translator. The declaration plugin supplies useful information that Core expressions alone do not capture.
- Keeping properties in Haskell source and mapping feedback back to those properties is a strong product direction. The comment plugin uses GHC's lexer, and the quasi-quoter records source locations.
- The repo takes silent mistranslation seriously. The explicit refusals for ambiguous instance methods and erased-newtype instances are good examples. The limitation documentation contains concrete failure cases rather than just a list of aspirational features.
- There is substantial regression coverage: 861 `#guard`-prefixed lines in `Tests/Unit.lean`, including behavioral checks for division signs, argument order, and instance dispatch. These are guard counts, not independent semantic coverage measurements.
- The named `Hs` runtime helpers provide a useful place to state and prove correspondence lemmas. Generated definitions remain readable enough to inspect and to use in manual proofs.

**Release blockers, in priority order.**

1. **Accepted programs can have different observable results.** `Maps.lean:244` maps both Haskell `Int` and `Integer` to unbounded Lean `Int`, and `Word` to `Nat`. The distinction matters for overflow and conversion. `Runtime.lean:22` also replaces a zero-stride infinite enumeration with `[]`, under an incorrect claim that every total observation of that list is bottom. A finite prefix is a total observation.

   I compiled this actual Haskell source through GHC 9.2.7's pass-0000 dump, the existing shim, and the existing transpiler:

   ```haskell
   inc :: Int -> Int
   inc x = x + 1

   takeOne :: [Int]
   takeOne = take 1 [1,1..2]
   ```

   | Observation | GHC on this 64-bit machine | Generated Lean |
   |---|---|---|
   | `inc 9223372036854775807` | `-9223372036854775808` | `9223372036854775808` |
   | `takeOne` | `[1]` | `[]` |

   Both generated results were proved with `by decide`; `#print axioms` reported no axioms for either theorem. This isolates translation fidelity from solver trust. Temporary evidence is in `/tmp/ProductionAuditProbe.hs`, `.json`, and `.lean`.

   **Required change:** distinguish machine integers from mathematical integers; implement exact width-sensitive semantics or require proved range conditions for an abstraction. Reject potentially infinite producers in the initial finite-data subset unless their observation semantics are modeled correctly. Calling a default value “sound bottom” does not establish a compositional correctness theorem.

2. **Proof acceptance currently includes admissions.** `Emit.lean:665` generates `decreasing_by all_goals sorry` for recursive definitions. The successful library build reports admitted declarations in the committed Fibonacci spikes. Separately, the installed pinned Blaster tactic defines `blasterProven : ∀ {α : Sort u}, α` and uses it for successful solver results (`Blaster/Command/Tactic.lean:33`). Upstream also documents the lack of proof reconstruction. [Blaster documentation](https://github.com/input-output-hk/lean-blaster)

   **Required change:** remove automatic termination admissions from the strict path. Generate real termination obligations and accept structural recursion, supplied proofs, or explicitly modeled partial computations. Expose separate statuses for kernel-checked proofs and trusted SMT results. Audit each reported theorem's transitive axiom dependencies, including user annotations; a grep for the token `sorry` is insufficient. Kernel checking still establishes a theorem about the Lean model, so the translation itself remains a separate trust boundary.

3. **The editor can display success without completed verification.** `vscode-extension/src/extension.ts:128` waits for a quiet diagnostic interval, which can occur before elaboration starts or finishes. At line 270, an active extension plus no current error diagnostics makes otherwise unclassified blocks green. Neither condition proves completion for the current document version. A `sorry` warning is also not an error, and failed pipeline runs do not invalidate all previous outcome caches. Compilation failures are labeled “Falsified” in CodeLens even when no counterexample exists. These are code-inspection findings; I did not run a VS Code integration test.

   **Required change:** drive both CLI and IDE from one structured verification result with source hash, run ID, property identity, completion state, and trust status. Distinguish pending, proved, SMT-valid, refuted, unknown, unsupported, and infrastructure error. Invalidate old results on edits, cancellation, and failed runs. For a refuted translated property, replay the counterexample against Haskell when possible before presenting it as a Haskell counterexample.

4. **The current CI example loop contradicts the fixtures.** `.github/workflows/lean_action_ci.yml:65` expects every `.hs` under examples to transpile and build successfully. Tracked examples such as `NewtypeInstances.hs` and `UserClassEqWithEq.hs` explicitly require transpilation to fail. There is no classification in the loop. The main Lake default target is just the executable; make the library/unit target explicit instead of relying on an action's defaults.

   **Required change:** create an enumerated fixture manifest with expected outcomes: verified, refuted, unsupported, and compile error, including the expected diagnostic and phase. CI should run `lake build GhcCoreToLean ghccoretolean`, positive and negative end-to-end tests, differential tests, and extension checks. Test that every recorded property receives exactly one outcome and that an empty property set cannot silently satisfy a verification job requiring properties.

5. **Information is erased before later phases need it.** `Lower.lean:27` removes type and dictionary arguments; the emitter then needs `rawBinds`, body-shape heuristics, and several independent method attribution passes to recover dispatch. `shim/decl-plugin/GhcDeclDump.hs:83` omits datatype parameters and uses unqualified type names. The 4,346-line emitter handles semantic reconstruction, validation, name resolution, and string emission. Cross-module collisions and newtype restrictions follow directly from these information losses.

   **Required change:** introduce a versioned, typed intermediate representation carrying package/module-qualified identities, local uniques, type parameters, superclass predicates with their arguments, dictionary selections, relevant coercions, and declaration origins. Resolve dispatch explicitly before erasure. Preserve separate newtype identities where required. Split semantic analysis from pretty printing; resolve names/types in the IR instead of replacing substrings of generated Lean. Validate supported constructs before emission, with source-local diagnostics. Parameterized ADTs and cross-module class support should follow this foundation.

6. **The driver is a repository demo runner, not yet a project tool.** `transpile.sh:64` uses one shared `.transpile-sandbox`; line 149 uses a global `/tmp/transpile-ext-types.tsv`, and per-module JSON paths are also global. During this audit the staged project changed to `StringBasics` while the audit run was in progress, and the audit module had no dump. The source of that external change was not established. The shared paths are enough to make simultaneous runs unsafe.

   The driver also synthesizes a new Cabal library with a fixed dependency list, losing the real project's components, package dependencies, flags, source directories, and build configuration. Import discovery is regex-based. The executable opens a namespace that the shell must close, and output plus source maps are separate non-atomic writes.

   **Required change:** use unique work directories, atomic artifact publication, bounded subprocesses, cancellation, and input fingerprints. Integrate with the actual Cabal build/component configuration and GHC module graph. Provide one `verify` command with documented exit codes and JSON output. Follow with content-addressed caching, stable source maps, supported-platform smoke tests, release packaging, and an explicit project license (no tracked root license was found). Keep toolchains pinned initially; version breadth can follow reproducibility.

**A production scope that can be delivered.**

Start with pure library functions over mathematical `Integer`, booleans, finite inductive data, and explicitly supported class operations. Require checked recursion and explicit domain conditions for partial operations. Add exact machine arithmetic as a separately tested capability. IO, arbitrary lazy streams, GADTs, and the whole of Hackage need not be prerequisites for a useful first release.

Write a semantic contract before adding further mappings. A possible shape, to formalize rather than claim today, is:

```text
Accepted(p) ∧ RelatedInputs(x, xL) ∧ Domain(p, x)
  ⇒ HaskellEval(p, x) terminates with v
    ∧ RelatedResults(v, LeanEval(translate(p), xL)).
```

Specify the relation at higher-order types and class dictionaries, the finite/total input restriction, and what establishes `Domain`. If only partial correctness is supported, state the weaker implication with source evaluation as a premise and do not claim termination. A bounded interpreter with fuel models bounded execution; it must not be presented as an unbounded proof.

| Phase | Deliverable | Exit condition |
|---|---|---|
| 1: Honest results | Semantic contract, strict acceptance checks, admission audit, classified fixture runner, versioned result protocol | The two mismatches above are faithfully modeled or rejected; incomplete, stale, admitted, or missing results cannot be reported as kernel-checked Haskell verification |
| 2: Reliable translation | Typed IR, preserved identities and dictionary dispatch, datatype parameters, explicit runtime contracts | Generated and curated differential tests agree with GHC on accepted terminating inputs; unsupported cases give stable diagnostics |
| 3: Useful project integration | Real Cabal components, isolated runs, atomic results, cancellation, CLI/IDE parity | A fresh supported environment verifies an external multi-module project; concurrent runs and changed dependencies cannot reuse stale evidence |
| 4: Evidence and release | Independent case studies, benchmark artifact, documentation, packaging | Another person reproduces all reported results from a clean checkout with pinned dependencies |

These are ordered gates, not calendar estimates. Differential testing provides strong empirical evidence, not a proof of semantic preservation. Prove correspondence lemmas for the small runtime and translation fragment in parallel with the engineering work.

**The paper has a plausible direction, but the novelty needs care.**

“Haskell to Lean” already exists: Talitha Holcombe's 2025 thesis describes HS-TO-LEAN using `ghc-lib-parser`, a common AST, a total Haskell fragment, and a heapsort case study. [Thesis](https://digitalcommons.chapman.edu/eecs_theses/3/)

Nor is using GHC Core to reach a proof assistant new: Abel et al. translated through Core into monadic Agda models supporting total or partial values. [Verifying Haskell Programs Using Constructive Type Theory](https://zls.mimuw.edu.pl/~ben/Papers/monadic.pdf)

The other essential comparisons are hs-to-coq's shallow embedding of total Haskell and LiquidHaskell's approach to laziness, termination, and SMT verification. The latter explicitly addresses why ordinary verification-condition generation can be unsound under lazy evaluation. [Total Haskell is Reasonable Coq](https://arxiv.org/abs/1711.09286), [Refinement Types for Haskell](https://simon.peytonjones.org/refinement-types-for-haskell/)

My proposed contribution is a practical verification workflow for existing Haskell libraries, with **explicit preservation of Core dictionary behavior, an enforced semantic subset, auditable proof assumptions, and source-linked feedback**. Each claimed distinction needs comparison with the implementations above; this initial literature check does not establish novelty or completeness.

Working title: **From GHC Core to Lean: Practical Verification with Explicit Semantic Contracts**.

Working pitch, describing the intended paper rather than completed results: Existing Haskell libraries contain desugared features and implicit dictionary choices that complicate translation into a proof assistant. We investigate a GHC Core to Lean workflow that preserves these choices within a defined fragment and reports the assumptions behind each verification result. The paper will describe the intermediate representation, translation obligations, source annotation workflow, and evidence from independent libraries. It will evaluate translation fidelity, proof effort, automation, and failure reporting, including adversarial programs that expose incorrect arithmetic, laziness, and instance mappings.

The paper should answer three questions:

1. Which properties and programs transfer faithfully, and what semantic assumptions or obligations make the transfer valid?
2. How much manual adaptation and proof effort is needed for existing libraries, including realistic class instances and module boundaries?
3. Does the integrated workflow find real bugs and give useful feedback at acceptable cold-build and edit-cycle costs?

Use three case-study families: arithmetic/domain invariants (the Ratio examples are a starting point), recursive finite data requiring induction, and an independently maintained multi-module library with custom instances. Keep the original source, report every adaptation, and include both true and deliberately false properties. Count attempted programs and rejected cases, not just successful translations. Tautological properties that repeat the implementation and concrete `decide` examples are useful regressions but insufficient as the evaluation.

Record translation coverage, rejection reasons, generated obligations, automatic versus manual proofs, axiom dependencies, bugs found, replayable counterexamples, annotation/proof LOC, translation time, proof time, and peak memory. Separate kernel-checked proofs from trusted SMT outcomes. Compare common tasks with HS-TO-LEAN, hs-to-coq, and LiquidHaskell where their supported fragments overlap; report version/tooling failures fairly. Preserve differential-test seeds and minimized counterexamples, exact revisions, solver settings, and clean-environment reproduction scripts.

Suggested outline: motivating library and bug; supported semantics and trust boundary; Core extraction and typed IR; translation and key correctness lemmas; verification and IDE workflow; comparative evaluation; limitations and related work. Draft the semantic contract, related work, and experimental protocol now; write claims and quantitative abstract results after the experiments.

For an engineering and experience contribution, a future Haskell Symposium submission is a natural target; its scope includes practical experience and tools. A CPP submission becomes more persuasive with mechanized translation/runtime correspondence and substantial proof case studies. These are venue-fit recommendations, not claims that an upcoming deadline is available. [Haskell Symposium scope](https://icfp26.sigplan.org/home/haskellsymp-2026), [CPP scope](https://popl27.sigplan.org/series/CPP)

**Validation performed in this review.**

- `lake build GhcCoreToLean ghccoretolean`: passed, 201 reported jobs, including replayed cached results; the output includes `sorry` warnings in the spikes.
- `npm run compile` in `vscode-extension`: passed.
- The isolated GHC → CBOR → shim → JSON → Lean probe: both mismatches reproduced, generated theorems checked without axioms, Lean process exit 0.
- The ordinary driver probe did not complete: initially Cabal cache access required sandbox escalation; after escalation the shared staging directory had changed to another module. The successful semantic probe bypassed the driver and spec plugins, used isolated GHC output paths, and appended the two `decide` theorems to the actual generated definitions.
- No complete end-to-end example sweep, clean-container rebuild, CI service inspection, editor integration test, or performance benchmark was performed. CI and editor findings are distinguished above from executed tests.
