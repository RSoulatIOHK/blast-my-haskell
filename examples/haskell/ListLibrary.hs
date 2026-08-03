{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
module ListLibrary where

-- M1 Task 5: Int-indexed ops (take / drop / splitAt / replicate).
-- Haskell clamps a negative count to 0; the mapped Lean forms clamp with
-- `Int.toNat`, so the semantics match on the whole domain. Ground goals are
-- proved by `decide` (kernel evaluation); the quantified goal is Blaster's.

takeSome :: Int -> [Int] -> [Int]
takeSome n xs = take n xs

dropSome :: Int -> [Int] -> [Int]
dropSome n xs = drop n xs

splitSome :: Int -> [Int] -> ([Int], [Int])
splitSome n xs = splitAt n xs

fill :: Int -> Int -> [Int]
fill n x = replicate n x

{- @lean
theorem takeSome_example : takeSome 2 [1, 2, 3] = [1, 2] := by decide
-}

{- @lean
theorem takeSome_neg : takeSome (-1) [1, 2, 3] = [] := by decide
-}

{- @lean
theorem dropSome_example : dropSome 1 [1, 2, 3] = [2, 3] := by decide
-}

{- @lean
theorem dropSome_neg : dropSome (-1) [1, 2, 3] = [1, 2, 3] := by decide
-}

{- @lean
theorem splitSome_example : splitSome 1 [5, 6, 7] = ([5], [6, 7]) := by decide
-}

{- @lean
theorem splitSome_zero : ∀ (xs : List Int), splitSome 0 xs = ([], xs) := by blaster
-}

{- @lean
theorem fill_example : fill 3 9 = [9, 9, 9] := by decide
-}
