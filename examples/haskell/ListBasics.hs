{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
module ListBasics where
    import Prelude
    import Lean.Spec (lean)

    listConcat :: [Int] -> [Int] -> [Int]
    listConcat l1 l2 = l1 ++ l2

    doubleAll :: [Int] -> [Int]
    doubleAll = map (\x -> x + x)

    [lean|
    theorem concat_length :
        ∀ (l1 l2 : List Int),
        List.length (listConcat l1 l2) = List.length l1 + List.length l2 := by
            intro l1 l2
            induction l1 with
            | nil => simp [listConcat]
            | cons hd tl ih => blaster
    |]
