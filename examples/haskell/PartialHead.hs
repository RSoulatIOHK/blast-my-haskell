{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
module PartialHead where
    import Prelude

    firstOrZero :: [Int] -> Int
    firstOrZero [] = 0
    firstOrZero xs = head xs
