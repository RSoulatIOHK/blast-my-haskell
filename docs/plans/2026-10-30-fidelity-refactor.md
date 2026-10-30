# Fidelity refactor and verification roadmap

Status: in progress, 2026-10-30. This plan starts from the local
`feature/m4-strings-chars` working tree, including the uncommitted verification
CLI, safety checks, tests, and VS Code changes. The September verification and
editor milestones in this directory are implemented baselines, not new work.

## Goal and acceptance contract

Make the tool dependable for a stated fragment of pure Haskell library code.
The initial fragment is first-order functions over `Integer`, `Bool`, finite
algebraic data, and finite lists. Add exact 64-bit `Int` as a separately tested
capability. Recursion requires a checked termination argument or an explicitly
stated partial-correctness contract. Partial operations require proved domain
conditions. Every construct outside the accepted fragment receives a stable
`unsupported` result with a source location.

Specify the source-to-model relation before broadening the translator. The
initial partial-correctness obligation is:

```text
Accepted(p) ∧ RelatedInputs(x, xL) ∧ HaskellEval(p, x) ⇓ v
  ⇒ ∃ vL, LeanEval(translate(p), xL) ⇓ vL ∧ RelatedResults(v, vL)
```

State the observation relation for each type, the treatment of bottom and
exceptions, the target machine width, and the assumptions about imported
functions and dictionaries. A separate termination proof can upgrade a
partial-correctness claim to total correctness. The current Lean theorem audit
remains evidence about the translated model. Differential tests increase
confidence in translation; they are not a correspondence proof.
Record the elaborated theorem statement and its exact source annotation in the
report. A checked proof of a different proposition is a failed verification,
even if the translated functions themselves are faithful.

The result protocol records three independent facts: (1) whether source
translation was accepted under the semantic contract, (2) what Lean proved and
which axioms it used, and (3) whether the product policy accepts the combined
evidence. Keep `proved`, `smt_valid`, `admitted`, `assumed`, `refuted`,
`unsupported`, `error`, `timeout`, `stale`, and `no_properties` distinct. A
counterexample to the Lean model becomes a Haskell counterexample only after
replay against GHC. Keep the source-level claim explicitly conditional on the
translation trust boundary until a correspondence result covers that fragment.

## Delivery sequence

### 0. Preserve and reproduce the baseline

- Inventory and preserve every current tracked and untracked source change,
  including the locally modified Blaster checkout. Create reviewable commits
  or a recoverable snapshot before restructuring files. Record the exact GHC,
  Lean, Blaster, Z3, Cabal, Node, and container revisions.
- Run the existing Lean build, 14 Python tests, 27 Node tests, fixture corpus,
  and editor integration on a clean Linux environment. Record expected outcomes
  and wall times as artifacts. Repair the local macOS GHC/SDK linker setup as a
  separate environment issue; a macOS failure must not be counted as a
  translation failure.
- Pin the Haskell package plan and container/tool downloads sufficiently for a
  fresh machine to reproduce the run. Require a clean Blaster checkout in the
  release CI job. Decide and add the repository license before a public release.

**Exit:** a fresh checkout produces the same classified results, with no local
dependency patch or preexisting build products required.

### 1. Specify semantics and freeze the verifier protocol

- Write a machine-readable support table keyed by GHC primitive, type, and
  source feature. Each entry states the Haskell behavior, Lean image, domain,
  evidence, and refusal condition. Treat `Int` overflow, division, lazy lists,
  partial functions, Unicode, newtypes, and class dispatch as first-class cases.
- Version the GHC dump and verifier JSON schemas. Reject unknown tags, missing
  metadata, contradictory statuses, absent theorem blocks, dirty dependencies,
  and changed inputs. Give every annotation a stable ID and exactly one terminal
  outcome. Report translator assumptions separately from proof axioms.
- Make source locations and the trust boundary visible in CLI, JSON, and editor
  output. Preserve the exact annotation text, resolved declaration identities,
  and elaborated theorem statement. Keep model proofs and trusted SMT outcomes
  visually distinct.

**Exit:** every current positive and negative fixture has a declared contract
entry and a stable result; no incomplete run can report success.

### 2. Replace information-loss recovery with a typed, versioned IR

- Extend extraction from GHC Core and declaration metadata to preserve package
  and module-qualified identities, binder uniques, type parameters, kinds,
  dictionary applications/selections, coercions, instance heads, and source
  provenance. Decode into a versioned IR with validation at the boundary.
- Split translation into explicit passes: validate source fragment; resolve
  names and class dispatch; lower supported Core operations; construct typed
  Lean declarations; emit Lean syntax and source maps. Each pass has a typed
  input/output and structured diagnostics. Preserve the original Core alongside
  the lowered form for audit.
- Retire substring-based name repair and spec rewriting as the new typed path
  reaches parity. Parse annotations as Lean syntax with explicit bindings or
  require qualified names, rather than guessing identifiers from text.
- Migrate one semantic slice at a time. Run the old and new translators on the
  same corpus, compare normalized Lean behavior and diagnostics, and retain
  each slice only after the fidelity gate passes. Break up the 5,000-line
  `Emit.lean` around these pass boundaries.

**Exit:** no supported class or cross-module reference depends on erased type
arguments or unqualified-name heuristics; ambiguous cases refuse with a source
location before Lean emission.

### 3. Establish runtime and proof correspondence for the core fragment

- Define and test Lean images for the initial data types and operations. Prove
  local correspondence lemmas for runtime helpers. Add exact `Int64` arithmetic
  and conversions with boundary cases; document target-width assumptions.
- Represent partiality and recursion explicitly. Replace generated
  `decreasing_by ... sorry` with checked termination obligations or a declared
  partial-correctness model. Refuse any result whose required assumption is
  absent. Audit transitive theorem axioms after elaboration.
- Prove a translation theorem for a deliberately small Core subset, then extend
  it by constructor/operation. Record which accepted features have mechanized
  correspondence and which depend on tested translator assumptions.

**Exit:** the initial fragment has kernel-checked examples, false-property
controls, and correspondence evidence; admitted termination never passes a
strict verification policy.

### 4. Integrate with actual Cabal projects and the editor

- Use the selected Cabal component and GHC module graph instead of generating a
  package with fixed `base` dependencies and regex import discovery. Preserve
  package flags, source directories, dependency identities, and exact compiler
  options in the run manifest.
- Keep each run isolated; publish source maps and generated artifacts atomically;
  support cancellation, deterministic timeouts, and content-addressed caching.
  Check source/dependency hashes immediately before accepting a result.
- Make the VS Code extension consume only completed versioned reports. Add
  precise invalidation for changed dependencies and keep errors in imported
  modules visible. Measure cold and edit-cycle latency on a real project.

**Exit:** a fresh multi-module library outside this repository verifies through
  the CLI and editor; concurrent and cancelled runs cannot display stale proof
  results.

### 5. Release evidence and broaden coverage deliberately

- Publish a support matrix, trust model, reproducible example project, versioned
  result schema, installation guide, and explicit limitations. Include one real
  bug or nontrivial invariant found in an independently maintained library.
- Add language features only through the fidelity gate below. Track acceptance
  rate, refusal reasons, source/proof annotation size, translation and proof
  time, memory, and solver trust. Use these measurements to choose the next
  fragment; add GHC-version adapters after the pinned version is stable.

**Exit:** an external user can reproduce the case study from a clean checkout
and tell exactly what was proved, what was trusted, and what was refused.

## CI fidelity gate

| Job | Runs | Blocking condition |
| --- | --- | --- |
| Fast checks | Lean library/executable, Python protocol tests, TypeScript/editor tests, schema validation, formatting | Any failure or invalid report |
| Classified end-to-end | Every tracked fixture, including expected proof, SMT, refusal, refutation, admission, typo, empty, timeout, stale, and collision cases | Missing fixture, changed expected status, or an unexpected accepted result |
| GHC differential | The same pinned GHC build and options versus generated Lean on accepted terminating inputs; fixed boundaries and recorded random seeds | Any mismatch, missing output, or unrepeatable failure |
| Semantic mutations | Deliberately wrong mappings and false properties that must make the gate fail | A mutation survives or a false property is accepted |
| Clean reproduction | Fresh pinned Linux image, clean Blaster dependency, no local build cache assumption | Different outcome from the baseline |
| Project integration | At least one external multi-module Cabal component | Failure to preserve component configuration or stale result |
| Editor contract | CLI-to-extension integration, cancellation, source edits, imported-file edits, trust changes | Green result without a completed matching report |
| Nightly depth | Wider seeds, fuzzing with minimized failures, performance and memory baselines, optional platform/version matrix | Report and triage regressions; promote stable cases to PR gate |

Every newly supported construct needs (a) a positive GHC observation, (b) a
boundary or adversarial case, (c) a deliberately false property, (d) a Lean
proof/axiom report, and (e) an explicit unsupported test for its remaining
domain. Annotation tests also verify that the elaborated proposition names the
intended source declarations. The differential runner currently covers three
`Int64` suites, two pure `Integer` suites, and one imported-module suite, and is
called by blocking CI. Expand it to class dispatch, broader module identities,
finite list inputs, and partiality. Save seeds, minimized
inputs, generated Lean, source hashes, and tool versions on every mismatch.

## Agent collaboration and review protocol

Use separate agents for: semantic contract and IR; GHC oracle and differential
tests; Lean/runtime proof and axiom audit; Cabal/CLI/editor integration. Assign
one owner per interface and land small vertical slices. A separate reviewer
tries to falsify each slice with source examples and checks the emitted Lean and
trust report. The author of a mapping does not approve its fidelity evidence.
Require an explicit decision for any change to the accepted fragment or proof
trust policy. Keep a short decision record with the GHC observation, Lean image,
assumptions, tests, and remaining gap. Agents can parallelize implementation;
the source-to-model contract and CI gates decide whether the work integrates.

## First build increment after this plan

1. Preserve the current working tree and produce a clean Linux baseline report.
2. Add `scripts/differential.py` to CI with its existing suites; make a
   deliberately wrong mapping fail the job to verify the gate itself.
3. Publish the support-table schema and a version-2 result contract that keeps
   source assumptions, Lean axioms, and SMT trust separate.
4. Begin the typed IR with `Integer`/`Bool` functions and one imported module;
   migrate this slice under old/new differential comparison.

This sequence produces useful fidelity evidence before the large emitter and
driver refactors, while retaining the working CLI and editor as comparison
oracles.

## Progress, 2026-10-30

- Preserved the original dirty tree and local Blaster patch in a private
  recoverable snapshot. Built a separate clean source clone for reproducibility.
- Local Lean library/executable, 15 Python tests, 27 editor tests, eight
  CLI-to-editor integration tests, and all 59 classified end-to-end fixtures
  pass. The integration suite had a stale `Overflow` refusal expectation;
  it now matches the current conservative proof fixture.
  With a temporary GHC package database pointing to Xcode SDK 26.5,
  `PureInteger` verified with one kernel proof and no theorem axioms. The
  original GHC package database points to incompatible Command Line Tools SDK
  27 stubs; no machine-wide toolchain setting was changed.
- The differential gate is now blocking in CI. All 459 local samples across
  six suites matched GHC, including pure integers, Boolean comparisons, finite
  integer lists, an imported module, and 64-bit arithmetic. A dedicated
  theorem-free canary passed normally, then reported
  GHC `3` versus generated Lean `1` after an addition-to-subtraction mapping
  mutation. Mismatch reports retain generated Lean source.
- Published `docs/semantics.md` and `docs/support-table.json` as the first
  conservative contract. Their wording keeps current Lean-model proof separate
  from unproved source correspondence. `docs/result-contract-v2.md` defines
  the next report interface; implementation and editor migration remain open.
- The shim now emits a versioned Core envelope with its module identity. The
  translator checks both before lowering. This is a boundary validation step,
  not yet the typed IR or a proof of imported-name resolution.
- The shim's `cabal.project.freeze` now pins the Cabal dependency solve and
  index state; the temporary per-run Haskell project copies it. This does not
  yet pin the container base image or every downloaded binary.
- CI now rejects a dirty or wrong-revision Blaster checkout. The check passes
  in the clean source clone and correctly rejects the original checkout's
  pre-existing local patch.
- A fresh macOS source snapshot built Lean and the shim with a clean
  pinned Blaster checkout. Its full fixture corpus passed 59/59, and the six
  differential suites passed 459/459. This narrows the remaining phase-0 gap
  to clean Linux and hosted CI reproduction, plus release pinning/licensing.
- The clean Linux container baseline remains open. Docker Desktop's disk
  allocation filled during GHC 9.2.7 installation even after unused build
  cache was pruned. Resolve capacity or use hosted CI before treating the
  container reproduction exit criterion as met.
- Exact local results and tool versions are recorded in
  `docs/baselines/2026-10-30-local.md`.
