module Overflow where
inc :: Int -> Int
inc x = x + 1

dec :: Int -> Int
dec x = x - 1

twice :: Int -> Int
twice x = x * 2

neg :: Int -> Int
neg x = negate x

isLess :: Int -> Int -> Bool
isLess x y = x < y

absInt :: Int -> Int
absInt x = abs x

{- @lean
-- GHC Int wraps at the target's signed 64-bit boundary.
theorem int_overflow : inc 9223372036854775807 = -9223372036854775808 := by
  simp [inc]

theorem int_underflow : dec (-9223372036854775808) = 9223372036854775807 := by
  simp [dec]

theorem int_multiplication_wraps : twice 4611686018427387904 = -9223372036854775808 := by
  simp [twice]

theorem int_negate_min_wraps : neg (-9223372036854775808) = -9223372036854775808 := by
  simp [neg]

theorem int_comparison_is_signed :
    isLess (-9223372036854775808) 9223372036854775807 = true := by
  simp [isLess]

theorem int_abs_min_wraps : absInt (-9223372036854775808) = -9223372036854775808 := by
  simp [absInt]
-}
