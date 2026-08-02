{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
module ListLiterals where

smallList :: [Int]
smallList = [1, 2, 3]

withPrefix :: [Int] -> [Int]
withPrefix xs = [1, 2] ++ xs

{- @lean
theorem smallList_val : smallList = [1, 2, 3] := by blaster
-}

{- @lean
theorem withPrefix_example : ∀ (x : Int), withPrefix [x] = [1, 2, x] := by blaster
-}
