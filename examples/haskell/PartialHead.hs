{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
module PartialHead where
    import Prelude

    firstOrZero :: [Int] -> Int
    firstOrZero [] = 0
    firstOrZero xs = head xs

[lean|
theorem firstOrZero_correct :
    ∀ (xs : List Int),
    firstOrZero xs = if List.null xs then 0 else List.head xs := by
        blaster
        ]