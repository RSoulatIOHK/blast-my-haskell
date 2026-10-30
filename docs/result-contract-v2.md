# Verification result contract v2 (design)

Version 1 reports one aggregate `status` and `accepted` flag. Version 2 will
keep three decisions separate so a Lean proof cannot be mistaken for a proof
that translation preserved Haskell behavior. This document is the interface to
implement; the current CLI and editor still emit and consume schema version 1.

## Required top-level records

| Record | Required contents |
| --- | --- |
| `subject` | Canonical entry path, SHA-256 of every translated source file, selected Cabal component, exact GHC flags, annotation IDs and source spans. |
| `toolchain` | GHC version and target width, Lean toolchain, package-plan hash, Blaster revision and dirty flag, translator/runtime/audit hashes, SMT version when used. |
| `translation` | `accepted`, `unsupported`, `error`, `timeout`, or `stale`; semantic policy; feature decisions; structured source assumptions; source maps; generated artifact hashes. |
| `proof` | One outcome per source annotation, its exact text, resolved declaration IDs, elaborated Lean proposition, theorem names, proof axioms, and diagnostics. |
| `policy` | Whether the completed run is accepted, the explicit SMT-trust choice, reasons, and the source claim (`lean-model` until correspondence is established). |

Each source assumption has a stable key from `support-table.json`, a source
span, the observed GHC operation or feature, the Lean image, and the evidence
used for that mapping. This list is separate from Lean theorem axioms. An
annotation has an ID derived from source path and span; the report keeps the
original annotation bytes as well as the elaborated proposition. A theorem
audit with the wrong proposition is a failed annotation, even if Lean checked
that proposition without axioms.

The `proof` outcome vocabulary is `proved`, `smt_valid`, `admitted`, `assumed`,
`refuted`, `unsupported`, `error`, `timeout`, `stale`, and `no_properties`.
`refuted` describes a counterexample to the Lean model until replayed against
GHC. `smt_valid` records Blaster's extra axiom and can pass product policy only
with explicit SMT trust. A source property cannot be labelled `proved` while
translation has only sampled differential evidence.

## Completion and acceptance invariants

1. Reject unknown schema versions, tags, missing required fields, duplicate
   annotation IDs, duplicate audits, and contradictory outcomes. Every source
   annotation has exactly one terminal outcome.
2. Compute `policy.accepted` only after all modules, annotations, and tool
   hashes have been checked. `translation.status` must be `accepted`; every
   required proof must be `proved`, or `smt_valid` with `trustSmt=true`.
3. Reject `admitted`, `assumed`, `refuted`, `unsupported`, `error`, `timeout`,
   `stale`, and `no_properties` under the strict policy. A missing proof block
   or silent Lean process cannot pass.
4. Recompute hashes for all source and generated files before acceptance.
   Dirty or changed dependencies fail the reproducible release policy. A
   diagnostic must include its source location and pipeline phase.
5. `translationCertified` remains false until a mechanized correspondence
   result covers the exact accepted fragment. Differential case counts and
   seeds are evidence fields, never substitutes for that result.

## Migration

Implement a schema validator and golden reports before changing the CLI.
Then add v2 output behind an explicit flag and run v1/v2 checks on the same
fixture corpus. Move the editor to v2 only after it rejects incomplete and
contradictory v2 reports. Remove v1 only after the external CLI contract and
extension have both migrated.
