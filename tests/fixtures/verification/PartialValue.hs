module PartialValue where
first :: [Integer] -> Integer
first = head
{- @lean
theorem model_empty : first [] = 0 := by decide
-}
