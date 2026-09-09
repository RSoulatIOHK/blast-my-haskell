{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
-- NEGATIVE fixture: transpilation MUST fail. `./transpile.sh
-- examples/haskell/CharSurrogate.hs` is expected to exit 1 with an error naming
-- BOTH offending binds (`lone` and `f`), the code point (`U+D800`) and the
-- surrogate as the reason, and to produce no
-- GhcCoreToLean/Generated/CharSurrogate.lean. Deliberately
-- EXCLUDED from the green-regression list, like StringSurrogate.hs,
-- NewtypeInstances.hs, TwoClassesSameMethod.hs, UserClassEqWithEq.hs and
-- UserClassNeqWithEq.hs.
--
-- THE SILENT-WRONG THIS PINS. `'\55296'` is U+D800, a lone surrogate. Haskell's
-- `Char` spans [0,0x10FFFF] INCLUDING the 2048 surrogates, so this is ordinary
-- Haskell; Lean's `Char` excludes them, so the literal has no Lean value at all.
-- The shim's `MachChar` arm used to emit `T.singleton c`, and `text-1.2.5.0`'s
-- `singleton` applies `safe` — so a surrogate arrived at Lean as U+FFFD, a
-- DIFFERENT and perfectly legal `Char`, with a green `lake build`. That loss was
-- latent for the whole project's life only because no dump had ever contained a
-- `LitChar`; this is the first fixture that produces one.
--
-- Contrast StringBasics.hs's `withNul`, the OTHER shape that fails a
-- standard-UTF-8 decode (modified UTF-8's overlong NUL `C0 80`) and is REPAIRED
-- rather than refused, because U+0000 *is* a legal Lean `Char`.
module CharSurrogate where

lone :: Char
lone = '\55296'

-- THE SECOND ROUTE, and the reason this fixture has two binds: PATTERN position.
-- For a STRING literal the emitter's pattern arm is dead-but-unproven (GHC
-- expands short string patterns into cons-chains before Core), but for a `Char`
-- it is ordinary Haskell — `f '\55296' = 1` unboxes to a `case` on `Char#` whose
-- alternative is `LitAlt (MachChar '\55296')`. So a surrogate can reach the
-- output without ever appearing in value position, and the refusal has to walk
-- `LitAlt` too. Measured in isolation before being folded in here: this bind
-- ALONE refuses (rc=1, naming bind `f`), so the route is covered end to end and
-- not merely by a unit guard on the walker.
f :: Char -> Int
f '\55296' = 1
f _        = 0
