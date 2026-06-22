{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}



module OperatorCommons where
    import Prelude
    import Ratio (CustomRatio(..), ceilRatio, integerMultRatio)
    import Lean.Spec (lean)

    operatorFee :: Integer -> Integer -> Integer -> CustomRatio -> Integer
    operatorFee tprice minFee maxFee feeRatio =
        min (max minFee (ceilRatio (integerMultRatio tprice feeRatio))) maxFee


    [lean|
    theorem operatorFee_positive :
        ∀ (tprice minFee maxFee : Int) (feeRatio : Ratio.CustomRatio),
        tprice > 0 → minFee > 0 →
        maxFee > 0 →
        operatorFee tprice minFee maxFee feeRatio >= 0 := by blaster
    |]


    -- Theorem that says that if you concat two lists, the length of the result is equal to the sum of the lengths of the two lists.
    listConcat :: [Int] -> [Int] -> [Int]
    listConcat l1 l2 = l1 ++ l2


    [lean|
    theorem list_concatenation_length :
        ∀ (l1 l2 : List Int),
        List.length (listConcat l1 l2) = List.length l1 + List.length l2 := by blaster
    |]