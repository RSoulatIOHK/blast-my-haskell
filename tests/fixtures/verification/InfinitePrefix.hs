module InfinitePrefix where
takeOne :: [Integer]
takeOne = take 1 [1,1..2]
{- @lean
-- A finite observation in Haskell is [1]. The old model returns [].
theorem model_prefix : takeOne = [] := by decide
-}
