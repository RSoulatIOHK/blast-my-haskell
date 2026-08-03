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

-- M1 Task 6: zip family (zip / zipWith / unzip).
-- Haskell's zip/zipWith truncate to the SHORTER list; so do Lean's, and both
-- recurse structurally on the two lists (no accumulator), so the mapped forms
-- reduce the same way in proofs. `unzip [] = ([], [])` on both sides.

pairUp :: [Int] -> [Int] -> [(Int, Int)]
pairUp xs ys = zip xs ys

addWise :: [Int] -> [Int] -> [Int]
addWise xs ys = zipWith (+) xs ys

-- Non-commutative op: `addWise` alone would pass even if the two list
-- arguments were swapped, so pin the order with subtraction too.
subWise :: [Int] -> [Int] -> [Int]
subWise xs ys = zipWith (-) xs ys

split2 :: [(Int, Int)] -> ([Int], [Int])
split2 ps = unzip ps

{- @lean
theorem pairUp_example : pairUp [1, 2] [3, 4, 5] = [(1, 3), (2, 4)] := by decide
-}

{- @lean
theorem addWise_example : addWise [1, 2] [10, 20] = [11, 22] := by decide
-}

{- @lean
theorem subWise_example : subWise [10, 20] [1, 2] = [9, 18] := by decide
-}

{- @lean
theorem subWise_trunc : subWise [10, 20, 30] [1, 2] = [9, 18] := by decide
-}

{- @lean
theorem split2_example : split2 [(1, 2), (3, 4)] = ([1, 3], [2, 4]) := by decide
-}

{- @lean
theorem pairUp_nil : ∀ (xs : List Int), pairUp xs [] = [] := by blaster
-}
