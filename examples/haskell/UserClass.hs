{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
module UserClass where
    import Prelude
    import Lean.Spec (lean)

    class Sized a where
        size :: a -> Int

    data Box = Box Int

    instance Sized Box where
        size (Box n) = n

    total :: Sized a => [a] -> Int
    total = foldr (\x acc -> size x + acc) 0

    boxTotal :: [Box] -> Int
    boxTotal = total

    [lean|
    theorem boxTotal_correct :
        ∀ (boxes : List Box),
        boxTotal boxes = total boxes := by blaster
    |]