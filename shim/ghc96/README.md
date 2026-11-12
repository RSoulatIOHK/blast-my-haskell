# GHC 9.6 Core dump adapter

This directory vendors `ghc-dump-core` 0.2.1.0 (Hackage archive SHA-256
`a9e54e06844fea2b5538158c10a70988b8074bb360a87fcd811331c8448d0b07`)
under its BSD-3-Clause license. The small patch set updates GHC API calls in
`GhcDump/Convert.hs` and `GhcDump/Plugin.hs` and permits GHC 9.6.6 with its
bundled `text` 2.0.2. The original GHC 9.2 shim project remains in `../`.

The adapter is used by `scripts/plutus_package_core.py` to dump Core during a
pinned `plutus-tx` Cabal build. The selected Core is then decoded by the same
`ghc-core-shim` JSON converter and checked by Lean. A successful dump alone is
not evidence that the translated Lean model is correct: the package gate also
requires Lean compilation, theorem axiom auditing, and differential execution.
