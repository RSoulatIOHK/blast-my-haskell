{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}

module Arithmetic where

data CustomRatio =
    CustomRatio {numerator :: Integer,
     denominator :: Integer} deriving (Show)

instance Eq CustomRatio where
    (CustomRatio n1 d1) == (CustomRatio n2 d2) =
        n1 * d2 == n2 * d1

addRatio :: CustomRatio -> CustomRatio -> CustomRatio
addRatio (CustomRatio n1 d1) (CustomRatio n2 d2) =
    CustomRatio (n1 * d2 + n2 * d1) (d1 * d2)

subRatio :: CustomRatio -> CustomRatio -> CustomRatio
subRatio (CustomRatio n1 d1) (CustomRatio n2 d2) =
    CustomRatio (n1 * d2 - n2 * d1) (d1 * d2)

{- @lean
theorem correct_add_sub : ∀ (r1 r2 : CustomRatio),
    addRatio r1 r2 == subRatio r1 (CustomRatio (-numerator r2) (denominator r2)) := by
  blaster
-}
