{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
module NewtypeBasic where

newtype Age = Age Int

mkAge :: Int -> Age
mkAge n = Age n

getAge :: Age -> Int
getAge (Age n) = n

addAges :: Age -> Age -> Age
addAges a b = Age (getAge a + getAge b)

{- @lean
theorem addAges_sum : ∀ (a b : Int), getAge (addAges (mkAge a) (mkAge b)) = a + b := by blaster
-}
