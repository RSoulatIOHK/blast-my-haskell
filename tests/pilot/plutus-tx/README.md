# `PlutusTx.List` source-slice pilot

The upstream source is [`PlutusTx.List` at commit `2f8edc6f01ebd6683c8494afeef026d1cab54713`](https://github.com/IntersectMBO/plutus/blob/2f8edc6f01ebd6683c8494afeef026d1cab54713/plutus-tx/src/PlutusTx/List.hs). Its SHA-256 is `91d0590e3ee1a47829a689600bf83a2cf22a561a142e74810062549c71095937`; the complete source is copied to `vendor/PlutusTx/List.hs` with the upstream Apache-2.0 license and notice. The `revAppend` and `reverse` declarations in `PlutusListPilot.hs` match that source byte for byte from signature through `INLINEABLE` pragma. The `Int` wrappers and Lean annotations belong to this pilot.

These functions use ordinary finite lists and no Plutus builtins. The pilot enables the `Strict` extension used by the upstream Cabal library and compiles the copied slice with the project's pinned GHC 9.2.7; it does **not** build the current `plutus-tx` Cabal package. Plutus lists GHC 9.6 as its primary compiler at this commit. A direct package-Core gate requires a supported-GHC extraction path before the claim can move from source slice to package.

The five Lean-model theorems are `rev_append_spec`, `reverse_model`, `reverse_involutive`, `reverse_length`, and `rev_append_length`. The first four are kernel checked with only the standard `propext` axiom in their current proofs. The last follows the generated Core recursion and uses Blaster for list-length arithmetic, requiring explicit `--trust-smt`; its audited axioms are `propext` and `Blaster.Tactic.blasterProven`. A compiler change may alter the generated helper ID in that proof, which must be reviewed rather than silently substituted.

The differential suite compares the `Int` wrappers with GHC on every pair of lists of length at most two over `{-1, 0, 1}` for `revAppendInt`, plus boundary probes and `reverseInt` cases. Local runs matched all 179 cases. These are sampled fidelity checks, not a translation-correctness certificate; `translationCertified` remains `false`. The laws hold for finite, fully defined lists; they do not assert behavior on bottoms or infinite lists.

Run the proof and fidelity gates with:

```bash
./verify.sh tests/pilot/plutus-tx/PlutusListPilot.hs --semantics conservative --trust-smt
python3 scripts/differential.py --report .lake/differential-results.json
python3 -m unittest tests.test_differential -v
```

Next, port Core extraction to a GHC version supported by this Plutus revision and build the original `plutus-tx` Cabal package with temporary dump instrumentation, as done for `data-ordlist`. The current `ghc-dump-core` 0.2.1.0 dependency does not compile with GHC 9.6.6: its `GhcDump/Convert.hs` imports the removed `GHC.Unit.Module.Name`. The annotation plugin also needs GHC parser API updates. Until the direct package gate passes, claims must be limited to this source-exact slice. Verification of compiled on-chain Plutus code additionally needs a separate Plutus compiler/UPLC correspondence argument.
