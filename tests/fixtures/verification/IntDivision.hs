module IntDivision where

quotByTwo :: Int -> Int
quotByTwo x = x `quot` 2

remByTwo :: Int -> Int
remByTwo x = x `rem` 2

divByTwo :: Int -> Int
divByTwo x = x `div` 2

modByTwo :: Int -> Int
modByTwo x = x `mod` 2

divByNegTwo :: Int -> Int
divByNegTwo x = x `div` (-2)

modByNegTwo :: Int -> Int
modByNegTwo x = x `mod` (-2)

divModByTwo :: Int -> (Int, Int)
divModByTwo x = x `divMod` 2

quotRemByTwo :: Int -> (Int, Int)
quotRemByTwo x = x `quotRem` 2

{- @lean
theorem quot_is_truncating : quotByTwo (-5) = -2 := by decide
theorem rem_follows_dividend : remByTwo (-5) = -1 := by decide
theorem div_is_flooring : divByTwo (-5) = -3 := by decide
theorem mod_follows_divisor : modByTwo (-5) = 1 := by decide
theorem negative_divisor_floors : divByNegTwo 5 = -3 := by decide
theorem negative_mod_follows_divisor : modByNegTwo 5 = -1 := by decide
theorem div_mod_pair : divModByTwo (-5) = (-3, 1) := by decide
theorem quot_rem_pair : quotRemByTwo (-5) = (-2, -1) := by decide
-}
