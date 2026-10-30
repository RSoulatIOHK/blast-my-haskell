-- A source-exact slice of data-ordlist 0.4.7.0, Data.List.Ordered.
-- Copyright (c) 2009-2011 Leon P Smith. See LICENSE in this directory.
-- The three *By definitions below are copied verbatim. The Int wrappers
-- after them are local test entry points, not upstream library definitions.
module OrderedPilot where

isSortedBy :: (a -> a -> Bool) -> [a] -> Bool
isSortedBy lte = loop
  where
    loop []       = True
    loop [_]      = True
    loop (x:y:zs) = (x `lte` y) && loop (y:zs)

memberBy :: (a -> a -> Ordering) -> a -> [a] -> Bool
memberBy cmp x = loop
  where
    loop []     = False
    loop (y:ys) = case cmp x y of
                    LT -> False
                    EQ -> True
                    GT -> loop ys

insertSetBy :: (a -> a -> Ordering) -> a -> [a] -> [a]
insertSetBy cmp = loop
  where
    loop x [] = [x]
    loop x (y:ys) = case cmp x y of
            LT -> x:y:ys
            EQ -> x:ys
            GT -> y:loop x ys

isSortedInt :: [Int] -> Bool
isSortedInt = isSortedBy (<=)

memberInt :: Int -> [Int] -> Bool
memberInt = memberBy compare

insertSetInt :: Int -> [Int] -> [Int]
insertSetInt = insertSetBy compare

{- @lean
theorem insert_empty (x : Int64) : insertSetInt x [] = [x] := by rfl
theorem member_empty (x : Int64) : memberInt x [] = false := by rfl
theorem sorted_empty : isSortedInt [] = true := by rfl
-}
