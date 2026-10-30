# Verification CLI and trust policy

Build `lake build GhcCoreToLean ghccoretolean` and `(cd shim && cabal build)`
before running `./verify.sh SOURCE.hs`. The command checks a freshly translated
Lean model in private directories. A successful result does not certify the
translation from Haskell to Lean.

**Semantic policy.** The default `--semantics conservative` models Haskell
`Int` as Lean `Int64`, including signed 64-bit wrapping for arithmetic. The
pipeline reads `ghc-9.2.7 --info`, records the target platform and bit width in
the result, and refuses conservative translation unless the measured target is
64-bit. Mathematical Haskell `Integer` remains Lean `Int`.

The exact `Int` surface includes arithmetic, signed comparison, `abs`, ordinary
finite ranges, `gcd`/`lcm`, conversion to and from `Integer`, `fromIntegral`
between those two types, and the list-count adapters. `quot`/`rem` and
`div`/`mod` preserve their distinct truncating and flooring rules when the Core
contains a statically nonzero divisor; zero, a dynamic divisor, and the
`minBound / -1` overflow remain explicit refusals.

Conservative mode still rejects `Word`, floating point and other fixed-width
types, mapped partial operations without checked domain conditions, potentially
infinite stepped enumeration, and translation warnings. Checks run on the
filtered Core before type/dictionary erasure, and also inspect datatype fields,
class methods, and instance heads. This is deliberately incomplete: even a safe
use of `head` is currently refused.

Passing these checks only excludes a known set of approximations. It does not
prove a semantic correspondence theorem, establish that all dictionaries were
translated correctly, or model general Haskell laziness. These remain explicit
limitations of the translator.

`--semantics approximate` enables the existing mappings for investigation and
regression work. In this mode a proof can be true of the Lean model and false
of the original Haskell program. In particular, `Int` has unbounded arithmetic
and a zero-stride infinite enumeration becomes `[]`. Every result records the
selected policy and `translationCertified: false`.

**Proof policy.** After elaboration, `#ghc_audit` enumerates theorem declarations
in the generated module and collects their transitive axioms from both their
statements and proofs. Declaration ranges associate theorems with annotation
blocks. The whole Lean subprocess must finish successfully; a quiet diagnostic
stream or a `Valid` log message is insufficient. The checker sets
`autoImplicit false` so a misspelled property name cannot silently become a
universally quantified variable.

| Status | Meaning | Can exit 0? |
|---|---|---|
| `proved` | Lean theorem dependencies use only the standard allowed axioms, or none | Yes |
| `smt_valid` | Depends on `Blaster.Tactic.blasterProven` | Only with `--trust-smt` |
| `admitted` | A theorem depends on `sorryAx`, including admitted termination | Never |
| `assumed` | A theorem depends on another nonstandard axiom | Never |
| `refuted` | Blaster refuted a property of the Lean model | Never |
| `no_theorem` | An annotation block contains no named theorem/lemma | Never |
| `no_properties` | The requested module has no annotation blocks | Never |
| `unsupported` | Translation or conservative-policy refusal | Never |
| `error` | GHC/Lean/setup/protocol failure, including unsuccessful proof elaboration | Never |
| `timeout`, `cancelled`, `stale` | Incomplete run or changed inputs/tools | Never |

The standard allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`.
The complete axiom list is still reported. An arbitrary user axiom, `native_decide`
axiom, or termination admission is not silently placed on the allowlist.
The existing emitter still inserts some termination admissions; the verifier
detects and rejects properties depending on them. It does not repair them.

An unannotated dependency may elaborate successfully. An annotated dependency
must satisfy the same proof policy as the entry module. Each annotation block
must contain at least one named theorem/lemma. Support declarations can share
a block with a theorem. A block containing only `#eval`, a definition, or an
anonymous `example` is not counted as a verified property.

**Protocol.** `./verify.sh SOURCE.hs --json` prints one JSON object. Exit 0 means
`accepted: true`; all other outcomes exit 1. Invalid CLI arguments exit 2.
Set `GHCCORE_PROGRESS=1` to receive `GHCCORE_PROGRESS:` JSON phase events on
stderr while keeping stdout as one completed result. The editor enables these
events for live progress; they never determine verification acceptance.
The default whole-run wall-clock limit is 600 seconds, configurable with
`--timeout`. Cancellation or timeout terminates subprocess groups, including
GHC/Lean/solver descendants.

Version 1 records `runId`, `source`, `semantics`, `trustSmt`, `claim: lean-model`,
`translationCertified`, `status`, `phase`, `accepted`, `elapsedSeconds`, and
`modules`. Each checked module records source and generated SHA-256 hashes,
source map, diagnostics, and per-block theorem names/axioms/statuses. Toolchain
metadata includes the requested Lean/GHC versions, dependency revisions,
the measured target platform and `Int` width, transpiler/runtime/audit hashes,
and whether the Blaster checkout is dirty.
Results from a dirty dependency are not clean-checkout reproducibility evidence.

Diagnostic filenames refer to temporary artifacts removed at completion; the
embedded source map and Haskell paths identify the original source. Sources are
hashed when staged and checked again before acceptance. Artifacts from another
run are never used as generated-module inputs. Support modules come from the
installed Lake build and are part of the trusted environment.

**Export and editor compatibility.** `transpile.sh SOURCE.hs [OUTPUT.lean]`
still exports models for manual Lean work, using the approximate policy by
default. Every run stages GHC inputs, dumps, specs, and manifests privately.
Export waits until all modules translate, serializes concurrent exporters, and
atomically replaces individual files. The `.lean` and `.map.json` pair is not a
transaction; verification never consumes those shared exports.

The VS Code extension now invokes `verify.sh --json` and waits for the process
and its output streams to close. It validates the schema, selected policy,
source identity, exit/acceptance agreement, and theorem/axiom status consistency.
It never infers success from LSP silence or solver log messages. Its defaults
match the CLI: conservative semantics and no implicit SMT trust.

Green means a proved property in an accepted Lean-model run. SMT results remain
amber, including explicitly trusted SMT; admissions, extra axioms, unsupported
inputs, and incomplete runs are distinct outcomes. Hovers include theorem
axioms, model policy, and available Lean diagnostics. Errors outside annotation
blocks and in imported modules remain visible in Problems and output.

Editing a Haskell buffer, changing a watched Haskell source, changing verifier
settings, starting a newer run, or clearing results invalidates previous editor
results and cancels active work. The editor rechecks source hashes and refuses
dirty imported buffers. Invalidation currently clears all results on any
Haskell edit; finer dependency tracking is future work. The editor uses the
Haskell file's workspace folder for relative settings and watches returned
imports outside that folder too. It does not require the Lean4 extension.
See [extension setup and settings](../vscode-extension/README.md).

The build driver still synthesizes a small Cabal library with the existing
fixed dependencies and uses the existing source-root/import discovery helper.
It is not yet integration with arbitrary Cabal projects. Fresh private builds
trade incremental speed for isolation; artifact caching is future work.

**Regression and paper artifacts.** Run:

```bash
lake build GhcCoreToLean ghccoretolean
python3 -m unittest discover -s tests -v
python3 scripts/check_fixtures.py --jobs 2
python3 scripts/differential.py --report .lake/differential-results.json
```

`tests/fixtures.json` classifies every tracked Haskell example and the dedicated
verification cases. A correct refusal/refutation passes its regression test but
does not become an accepted verification. The runner rejects unclassified
tracked examples, selects subsets with `--only`, and writes the full report to
`.lake/verification-results.json` (or `--report PATH`). Untracked exploratory
examples are not automatically included in CI. The deliberately false
`UserClass` property and admitted `FibComplex` property are retained as explicit
negative outcomes. These reports are the initial reproducible experiment format
for the paper, not a measurement of real-world library coverage.

The differential gate runs Haskell functions with pinned GHC 9.2.7 and compares
their outputs with the freshly translated Lean definitions under conservative
semantics. `tests/differential.json` records boundary cases and deterministic
random seeds for machine `Int`, arbitrary precision `Integer`, Boolean
comparisons, finite integer lists (including list inputs), and one imported module.
The [data-ordlist pilot](../tests/pilot/data-ordlist/README.md) adds three
source-exact ordered-list functions with monomorphic `Int` entry points. Its
empty-list lemmas, insertion membership, and sortedness preservation are kernel
checked in CI for the generated Lean model. A mismatch, missing
case, or translation error fails CI and saves the case-level report as an artifact.
On a value mismatch, the runner also retains the generated Lean source under
`.lake/differential-artifacts/<runId>/`; the report records its exact path.
CI also replaces the `GHC.Num.+` mapping with subtraction in its disposable checkout,
then requires the one-case canary to report an actual GHC/Lean mismatch. These
sampled comparisons test fidelity; they do not certify the translator.
The shim's Core JSON now carries `schemaVersion: 1` and the originating module
name. Pipeline translation requires both and rejects an unknown version or a
module mismatch before lowering; legacy unversioned dumps remain readable
only through the two-argument manual translator form during migration.
For a local GHC installation whose global package database points at an
incompatible macOS SDK, `--oracle-package-db PATH` applies a temporary package
database only to the direct GHC oracle build and records the path in the report.
