{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
module ListLibrary where

import Data.Maybe (fromMaybe)

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
theorem pairUp_nil : ∀ (xs : List Int), pairUp xs [] = [] := by blaster
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
theorem split2_nil : split2 [] = ([], []) := by decide
-}

-- M1 Task 7: folds and predicates (sum / product / all / any / and / or),
-- plus a list comprehension. Haskell `sum = foldl (+) 0`, `product =
-- foldl (*) 1`, `and [] = True`, `or [] = False`, `all p [] = True`,
-- `any p [] = False` — the mapped Lean forms agree on all of these.
-- The Bool-valued goals are written `= true` / `= false` (Lean `Bool`
-- literals, not the `Prop` `True`/`False`).

sumList :: [Int] -> Int
sumList xs = sum xs

prodList :: [Int] -> Int
prodList xs = product xs

allPos :: [Int] -> Bool
allPos xs = all (> 0) xs

anyZero :: [Int] -> Bool
anyZero xs = any (== 0) xs

conj :: [Bool] -> Bool
conj bs = and bs

disj :: [Bool] -> Bool
disj bs = or bs

doubled :: [Int] -> [Int]
doubled xs = [2 * x | x <- xs]

{- @lean
theorem sumList_example : sumList [1, 2, 3] = 6 := by decide
-}

{- @lean
theorem sumList_singleton : ∀ (a : Int), sumList [a] = a := by blaster
-}

{- @lean
theorem prodList_example : prodList [2, 3, 4] = 24 := by decide
-}

{- @lean
theorem allPos_example : allPos [1, 2] = true ∧ allPos [1, 0] = false := by decide
-}

{- @lean
theorem anyZero_example : anyZero [1, 0] = true ∧ anyZero [1, 2] = false := by decide
-}

{- @lean
theorem conj_disj_empty : conj [] = true ∧ disj [] = false := by decide
-}

-- The non-empty companion to `conj_disj_empty`: `decide` only ever exercises
-- the `[]` base case of `Hs.and`/`Hs.or`, so this quantified version is what
-- actually covers the cons arms (and confirms Blaster unfolds both wrappers).
{- @lean
theorem conj_disj_nonempty : ∀ (b c : Bool), conj [b, c] = (b && c) ∧ disj [b, c] = (b || c) := by blaster
-}

-- RHS mixes `2 * (x + y)` with `x + x`: the differing surface forms for the
-- same value are deliberate, exercising blaster's arithmetic normalization
-- rather than a term-by-term syntactic match against the emitted body.
{- @lean
theorem doubled_example : ∀ (x y : Int), doubled [x + y, y, x] = [2 * (x + y), 2 * y, x + x] := by blaster
-}

-- M1 Task 8: search and flatten (elem / notElem / lookup / concat / concatMap),
-- plus a MULTI-generator comprehension. Haskell semantics being imaged:
-- `elem`/`notElem`/`lookup` compare with `Eq` (→ the project's `BEq`);
-- `lookup k [] = Nothing`; `concat [] = []`; `concatMap f = concat . map f`.
-- `lookupOr` also re-exercises the existing `fromMaybe` mapping, and
-- `dupEach`'s lambda body `[x, x]` routes through `GHC.Base.build`.

hasZero :: [Int] -> Bool
hasZero xs = elem 0 xs

misses :: Int -> [Int] -> Bool
misses x xs = notElem x xs

lookupOr :: Int -> [(Int, Int)] -> Int
lookupOr k ps = fromMaybe 0 (lookup k ps)

flattenAll :: [[Int]] -> [Int]
flattenAll xss = concat xss

dupEach :: [Int] -> [Int]
dupEach xs = concatMap (\x -> [x, x]) xs

pairsUpTo :: Int -> [(Int, Int)]
pairsUpTo n = [(x, y) | x <- [1 .. n], y <- [1 .. x]]

{- @lean
theorem hasZero_example : hasZero [1, 0] = true ∧ hasZero [1, 2] = false := by decide
-}

{- @lean
theorem misses_example : misses 3 [1, 2] = true := by decide
-}

-- The quantified companion: `decide` only ever exercises `contains` on concrete
-- Int literals, so this is what covers the cons arm with a symbolic element
-- (and confirms Blaster unfolds the `contains`/`elem` abbrev chain).
{- @lean
theorem misses_notElem : ∀ (x : Int), misses x [x] = false := by blaster
-}

{- @lean
theorem lookupOr_example : lookupOr 2 [(1, 10), (2, 20)] = 20 ∧ lookupOr 9 [(1, 10)] = 0 := by decide
-}

{- @lean
theorem flattenAll_example : flattenAll [[1], [2, 3]] = [1, 2, 3] := by decide
-}

{- @lean
theorem dupEach_example : dupEach [1, 2] = [1, 1, 2, 2] := by decide
-}

{- @lean
theorem pairsUpTo_example : pairsUpTo 3 = [(1, 1), (2, 1), (2, 2), (3, 1), (3, 2), (3, 3)] := by decide
-}
