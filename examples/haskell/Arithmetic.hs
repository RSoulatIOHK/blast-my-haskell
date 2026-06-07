{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}

module Arithmetic where

data CustomRatio =
    CustomRatio {numerator :: Integer,
     denominator :: Integer} deriving (Show)

instance Eq CustomRatio where
    (CustomRatio n1 d1) == (CustomRatio n2 d2) =
        n1 * d2 == n2 * d1


{- @lean
theorem correct_ratio : ∀ (r1 r2 : CustomRatio),
    r1 == r2 ↔ numerator r1 * denominator r2 == numerator r2 * denominator r1 := by
  intro r1 r2
  cases r1
  cases r2
  blaster
-}
