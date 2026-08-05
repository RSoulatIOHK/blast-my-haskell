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

{- @lean
theorem originDist_mk : ∀ (x y : Int), originDist (RecordOps.mkPoint x y) = x := by blaster
-}

{- @lean
theorem bumpAge_inc : ∀ (n : Int), bumpAge n = n + 1 := by blaster
-}
