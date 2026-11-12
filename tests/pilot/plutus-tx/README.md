# `PlutusTx.List` verification pilot

The upstream source is [`PlutusTx.List` at commit `2f8edc6f01ebd6683c8494afeef026d1cab54713`](https://github.com/IntersectMBO/plutus/blob/2f8edc6f01ebd6683c8494afeef026d1cab54713/plutus-tx/src/PlutusTx/List.hs). Its SHA-256 is `91d0590e3ee1a47829a689600bf83a2cf22a561a142e74810062549c71095937`; the complete source is copied to `vendor/PlutusTx/List.hs` with the upstream Apache-2.0 license and notice. The `revAppend` and `reverse` declarations in `PlutusListPilot.hs` match that source byte for byte from signature through `INLINEABLE` pragma. The `Int` wrappers and Lean annotations belong to this pilot.

These functions use ordinary finite lists and no Plutus builtins. The source-slice gate enables the `Strict` extension used by the upstream Cabal library and compiles the copied declarations with the project's pinned GHC 9.2.7. The separate package gate builds the pinned `plutus-tx` Cabal library with GHC 9.6.6, selects `revAppend` and `reverse` from its own Core dump, and compiles that translated model in Lean. The package source files are unchanged; the build temporarily adds the Core dump plugin to the Cabal manifest. The report records both manifest hashes.

The five Lean-model theorems are `rev_append_spec`, `reverse_model`, `reverse_involutive`, `reverse_length`, and `rev_append_length`. The first four are kernel checked with only the standard `propext` axiom in their current proofs. The last follows the generated Core recursion and uses Blaster for list-length arithmetic, requiring explicit `--trust-smt`; its audited axioms are `propext` and `Blaster.Tactic.blasterProven`. A compiler change may alter the generated helper ID in that proof, which must be reviewed rather than silently substituted.

The differential suite compares the `Int` wrappers with GHC on every pair of lists of length at most two over `{-1, 0, 1}` for `revAppendInt`, plus boundary probes and `reverseInt` cases. The package gate runs the same 179 inputs against the built Plutus library and the package-Core Lean model. These are sampled fidelity checks, not a translation-correctness certificate; `translationCertified` remains `false`. The laws hold for finite, fully defined lists; they do not assert behavior on bottoms or infinite lists.

Run the proof and fidelity gates with:

```bash
./verify.sh tests/pilot/plutus-tx/PlutusListPilot.hs --semantics conservative --trust-smt
python3 scripts/differential.py --report .lake/differential-results.json
python3 -m unittest tests.test_differential -v

# Requires GHC 9.6.6, Cabal, Lean, Z3, and network access to Hackage/CHaP.
python3 scripts/plutus_package_core.py --update-index
```

The package gate uses a patched GHC 9.6 adapter for `ghc-dump-core` 0.2.1.0. It builds `plutus-core` with optional inline-R, certification, and system-crypto components disabled and pins `text` 2.0.2; these build-profile choices are explicit in the generated Cabal project. Disabling system crypto lets the selected list functions build on CI without the Cardano C crypto libraries; it does not support claims about crypto builtins. `PackageProofs.lean` proves five laws directly about the package-Core model; the length law uses Blaster and requires `Blaster.Tactic.blasterProven`. CI checks the exact theorem set and permitted axioms. This establishes the selected laws for the checked Lean model, supported by package execution samples. Formal translation certification and verification of compiled on-chain Plutus code additionally need separate arguments.
