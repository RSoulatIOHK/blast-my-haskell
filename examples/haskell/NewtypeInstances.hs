{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
-- NEGATIVE fixture: transpilation MUST fail; exercised manually / by the M2
-- regression script's expected-fail list. It is deliberately EXCLUDED from the
-- green-regression list — `./transpile.sh examples/haskell/NewtypeInstances.hs`
-- is expected to exit NON-zero with an error naming `Eq` and `Celsius`, and no
-- GhcCoreToLean/Generated/NewtypeInstances.lean is produced.
--
-- Why: a newtype is erased to its underlying type, so an instance on one has no
-- Lean image. Before the guard, this module emitted
--   instance : BEq Int where beq := <the $c== body>
-- inside `namespace NewtypeInstances` — relocating Eq onto `Int` and silently
-- changing the meaning of every `==` on `Int` in the module, theorem text
-- included. See "Newtype-instance guard" in GhcCoreToLean/Emit.lean and the M2
-- Task 5 block in GhcCoreToLean/Tests/Unit.lean.
module NewtypeInstances where

newtype Celsius = Celsius Int

instance Eq Celsius where
  (Celsius a) == (Celsius b) = a == b

sameTemp :: Celsius -> Celsius -> Bool
sameTemp a b = a == b
