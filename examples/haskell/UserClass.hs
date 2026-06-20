{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
module UserClass where
    import Prelude

    class Sized a where
        size :: a -> Int

    data Box = Box Int

    instance Sized Box where
        size (Box n) = n

    total :: Sized a => [a] -> Int
    total = foldr (\x acc -> size x + acc) 0

    boxTotal :: [Box] -> Int
    boxTotal = total
