{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
module CaseBinder where
    import Prelude

    clampPos :: Int -> Int
    clampPos n = case n of
        0 -> 0
        _ -> if n < 0 then 0 else n
