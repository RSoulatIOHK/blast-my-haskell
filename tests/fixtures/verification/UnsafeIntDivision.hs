module UnsafeIntDivision where

unsafeDivide :: Int -> Int -> Int
unsafeDivide x y = x `div` y

divideByZero :: Int -> Int
divideByZero x = x `quot` 0

overflowingDivide :: Int -> Int
overflowingDivide x = x `quot` (-1)
