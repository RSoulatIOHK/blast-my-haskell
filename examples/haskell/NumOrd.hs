{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
module NumOrd where
    import Prelude
    classify :: Int -> Int -> Ordering
    classify a b = compare (signum a) (gcd a b)
    split :: Int -> Int -> (Int, Int)
    split a b = divMod a b
    combos :: Int -> Int -> (Int, Int)
    combos a b = quotRem a b
    multiple :: Int -> Int -> Int
    multiple a b = lcm a b
    toOrd :: Int -> Ordering
    toOrd a = if a < 0 then LT else if a > 0 then GT else EQ
