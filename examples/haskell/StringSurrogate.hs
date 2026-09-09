{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
-- NEGATIVE fixture: transpilation MUST fail. `./transpile.sh
-- examples/haskell/StringSurrogate.hs` is expected to exit 1 with an error
-- naming the bind `lone`, the offending bytes (`78 ed a0 80 79`) and the
-- surrogate as the reason, and to produce no
-- GhcCoreToLean/Generated/StringSurrogate.lean. Deliberately EXCLUDED from the
-- green-regression list, like NewtypeInstances.hs, TwoClassesSameMethod.hs,
-- UserClassEqWithEq.hs and UserClassNeqWithEq.hs.
--
-- THE SILENT-WRONG THIS PINS. `'\55296'` is U+D800, a lone surrogate. Haskell's
-- `Char` spans [0,0x10FFFF] INCLUDING the 2048 surrogates, so this is ordinary
-- Haskell; Lean's `Char` excludes them, so the literal has no Lean value at all.
-- GHC dumps it as modified UTF-8 (`ED A0 80`), which standard UTF-8 rejects, so
-- the shim's lenient decode yields `x???y` — five code points with three U+FFFD
-- where the source has three characters. Once M4 Task 2 mapped
-- `unpackCString#`/`unpackCStringUtf8#`, that decode would have been BELIEVED:
-- `length` 5 instead of 3, wrong content, and a green `lake build`.
--
-- Contrast `withNul` in StringBasics.hs, which is the OTHER modified-UTF-8
-- deviation (overlong NUL `C0 80`) and is repaired rather than refused, because
-- U+0000 *is* a legal Lean `Char`.
module StringSurrogate where

lone :: String
lone = "x\55296y"
