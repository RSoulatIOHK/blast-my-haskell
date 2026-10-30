module PureInteger where
inc :: Integer -> Integer
inc x = x + 1
{- @lean
theorem inc_value : inc 3 = 4 := by decide
-}
