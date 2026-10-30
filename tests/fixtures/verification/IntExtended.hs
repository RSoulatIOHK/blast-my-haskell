module IntExtended where

intGcd :: Int -> Int -> Int
intGcd = gcd

intLcmByTwo :: Int -> Int
intLcmByTwo x = lcm x 2

intRange :: Int -> Int -> [Int]
intRange lo hi = [lo .. hi]

intToInteger :: Int -> Integer
intToInteger = toInteger

integerToInt :: Integer -> Int
integerToInt = fromInteger

intToIntegerViaIntegral :: Int -> Integer
intToIntegerViaIntegral = fromIntegral

integerToIntViaIntegral :: Integer -> Int
integerToIntViaIntegral = fromIntegral

{- @lean
theorem int_range_exact : intRange (-2) 2 = [-2, -1, 0, 1, 2] := by
  decide-}

{- @lean
theorem int_gcd_min : intGcd (-9223372036854775808) 0 = -9223372036854775808 := by
  decide
-}

{- @lean
theorem int_lcm_wraps : intLcmByTwo 9223372036854775807 = 2 := by
  decide
-}

{- @lean
theorem int_to_integer_signed : intToInteger (-1) = (-1 : _root_.Int) := by
  decide
-}

{- @lean
theorem integer_to_int_wraps : integerToInt 18446744073709551616 = 0 := by
  decide
-}

{- @lean
theorem from_integral_to_integer :
    intToIntegerViaIntegral (-7) = (-7 : _root_.Int) := by
  decide
-}

{- @lean
theorem from_integral_to_int :
    integerToIntViaIntegral 18446744073709551617 = 1 := by
  decide
-}
