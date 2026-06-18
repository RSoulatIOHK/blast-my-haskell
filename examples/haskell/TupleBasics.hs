{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
module TupleBasics where
    import Prelude

    swapPair :: (Int, Int) -> (Int, Int)
    swapPair p = (snd p, fst p)

    mkPair :: Int -> Int -> (Int, Int)
    mkPair a b = (a, b)

    firstOf :: (Int, Int) -> Int
    firstOf (x, _) = x
