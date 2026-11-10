# Function verification work packet

Use one work packet per library function or closely related group. Keep the
source package, compiler version, semantic assumptions, property, and evidence
in the same review. The [`data-ordlist` pilot](../tests/pilot/data-ordlist/README.md)
is the first packet.

## Record before implementation

1. Pin the published Cabal archive and the target module with SHA-256 hashes.
   Record the package name, version, module, and selected exported functions.
2. State the domain on which each law holds. For ordered-list operations,
   distinguish finite sorted inputs from unsorted fidelity probes and state
   what comparator `EQ` means.
3. Name the permitted proof assumptions. A Blaster result is accepted only
   with explicit `--trust-smt` and an axiom audit; it does not certify the
   translation from Haskell to Lean.

## Evidence gates

Run these gates in order for the ordered-list packet:

```bash
lake build GhcCoreToLean ghccoretolean
( cd shim && cabal build )
python3 scripts/ordlist_package_fidelity.py
python3 scripts/ordlist_core_import.py
./verify.sh tests/pilot/data-ordlist/OrderedPilot.hs --semantics conservative --trust-smt
python3 scripts/differential.py
```

The package fidelity gate checks the source slice against the pinned archive
and compares its Haskell execution with the built package. The Core import gate
builds the actual Cabal package with temporary dump-plugin metadata, selects
the requested bindings and their top-level Core dependencies, compiles their
Lean model, compares package GHC/Lean execution, and audits laws proved over
that model. CI requires both gates and a changed-wrapper canary. A result is
reviewable only when its package, Core, generated Lean, theorem axioms, and
case-level reports are attached to the CI run.

## Collaboration and review

- Source reviewer checks archive hashes, module identity, copied definitions,
  and the law's input domain against the upstream package.
- Translation reviewer checks selected Core dependencies, conservative
  warnings, generated Lean, and counterexamples from differential tests.
- Proof author writes the Lean law, using Blaster where it can encode the
  goal, and records any explicit SMT trust.
- Final reviewer inspects the axiom report and CI canaries, then confirms that
  the stated claim matches the evidence before merging.

The roles can be handled by separate agents or sequential reviews. A failed
gate is a new work item with its smallest reproducing input; fixes are rerun
through the same gates. Keep `translationCertified: false` until a separate
translation-correctness argument is established.
