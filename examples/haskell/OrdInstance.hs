{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
module OrdInstance where
    import Prelude
    data Coin = Heads | Tails deriving (Eq, Ord)
    pick :: Coin -> Coin -> Coin
    pick a b = if a <= b then a else b
