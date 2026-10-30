# `data-ordlist` pilot

Target: [`data-ordlist` 0.4.7.0](https://hackage-content.haskell.org/package/data-ordlist-0.4.7.0), specifically `Data.List.Ordered`.
The published source archive has SHA-256
`6f6c1e7a9a9155ad78ca78cb9abd6f7e2e1c78b3e549b179dc0874e6428f490d`;
its `Data/List/Ordered.hs` has SHA-256
`73c11909892d3ce36dcab3688f5429b4db20ed752137a5d130f7ce3f00870aee`.
The BSD-3-Clause license is copied in [LICENSE](LICENSE).

[`OrderedPilot.hs`](OrderedPilot.hs) copies the complete definitions of
`isSortedBy` (upstream lines 82–87), `memberBy` (95–102), and `insertSetBy`
(136–143) verbatim. The `Int` wrappers are local entry points for the pinned
64-bit GHC target. This slice deliberately keeps the upstream algorithms
unaltered; a later milestone should import the Cabal package itself and preserve
module/package identity across the translation boundary.

The source contract assumes finite ordered lists for `memberBy` and
`insertSetBy`; `insertSetBy`'s set behavior also assumes no duplicate input
elements. `isSortedBy` accepts any finite list. The comparison functions must
obey the intended total order; the initial execution checks instantiate them
with GHC's `Ord Int` operations. The differential suite includes unsorted and
duplicate inputs as fidelity probes, without treating them as inputs to the set
theorems.

Milestone gates:

1. Translate this source slice under conservative semantics with no warnings or
   admissions; compare its `Int` wrappers against the same GHC source in CI.
2. Prove sortedness preservation and membership for insertion into a sorted set
   in Lean, with the proof's axiom report audited. The generated-model theorems
   `sorted_insert`, `member_insert`, and `insert_idempotent` now cover all finite
   `Int64` lists; the first uses `isSortedInt xs = true` as its premise. Their
   generic membership and idempotence proofs use Blaster after induction and
   comparison case splits. CI invokes `verify.sh --trust-smt` and requires
   `Blaster.Tactic.blasterProven` on exactly those two generic theorems and their
   `Int64` wrappers. The sortedness proof and the remaining helpers use only
   Lean's standard allowed axioms (`propext`, `Classical.choice`, and
   `Quot.sound`). Some of those helpers name GHC-generated local functions, so
   a compiler or source change can require proof maintenance.
3. Extend to `mergeBy` and `unionBy`, including sortedness and multiplicity
   properties. Their two-list recursion may need a termination measure.

Passing finite differential samples or proving a property of generated Lean
does not establish source-to-Lean correspondence. The global
`translationCertified` flag remains `false`.

## Blaster exploration

Run `python3 tests/pilot/data-ordlist/probe_blaster.py` after building the
toolchain. It translates the pinned source afresh, asks Blaster to prove the
generic insertion-idempotence induction cases, and tests a direct `Int64` goal.
At the pinned Blaster revision, the generic cases return `Valid` but depend on
`Blaster.Tactic.blasterProven`; the direct `Int64` goal is rejected because its
`BitVec` representation is unsupported. The CI proof gate now accepts Blaster's
SMT axiom for generic membership and idempotence under the explicitly trusted
policy. The standalone probe remains a way to inspect Blaster's capabilities.
Blaster currently performs no proof reconstruction; see its
[tactic documentation](https://github.com/input-output-hk/Lean-blaster#tactic).
