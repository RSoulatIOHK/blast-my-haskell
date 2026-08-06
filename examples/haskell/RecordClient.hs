{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
module RecordClient where

import RecordOps (Point, mkPoint, px)
import NewtypeBasic (Age, mkAge, getAge)

originDist :: Point -> Int
originDist p = px p

clientAge :: Int -> Int
clientAge n = getAge (mkAge n)

-- Imported newtype in the SIGNATURE: `Age` reaches this module's Core types,
-- so the erasure must cross the module boundary (Age → Int).
bumpAge :: Age -> Age
bumpAge a = mkAge (getAge a + 1)

{- @lean
theorem clientAge_id : ∀ (n : Int), clientAge n = n := by blaster
-}

-- `RecordOps.mkPoint` must be written QUALIFIED here: imported VALUE names in
-- `@lean` spec text are NOT auto-qualified (only type needles are, at pass 4), so
-- a bare `mkPoint` fails loud at `lake build`. Known limitation; the user-facing
-- statement is README's spec-notation bullet, "for imported symbols, qualify with
-- the module". See the M2 Task 6 note (c) in `GhcCoreToLean/Tests/Unit.lean`.
{- @lean
theorem originDist_mk : ∀ (x y : Int), originDist (RecordOps.mkPoint x y) = x := by blaster
-}

{- @lean
theorem bumpAge_inc : ∀ (n : Int), bumpAge n = n + 1 := by blaster
-}
