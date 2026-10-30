module PureCore where

isNegative :: Integer -> Bool
isNegative x = x < 0

duo :: Integer -> [Integer]
duo x = [x, x + 1]

chooseSmaller :: Integer -> Integer -> Integer
chooseSmaller x y = if x < y then x else y
