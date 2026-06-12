{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
module MaxMinOverArithmetics where

import Lean.Spec (lean)

min :: Int -> Int -> Int
min a b = if a < b then a else b

max :: Int -> Int -> Int
max a b = if a < b then b else a

[lean|
theorem max_over_sub :
    ∀ (a b c : Int), c - max a b = min (c - a) (c - b) := by blaster
|]

[lean|
theorem min_over_sub :
    ∀ (a b c : Int), c - min a b = max (c - a) (c - b) := by blaster
|]

[lean|
theorem max_over_sub_div :
    ∀ (a b c d : Int), d > 0 → (c - max a b) / d = min ((c - a) / d) ((c - b) / d) := by blaster
|]

[lean|
theorem min_over_sub_div :
    ∀ (a b c d : Int), d > 0 → (c - min a b) / d = max ((c - a) / d) ((c - b) / d) := by blaster
|]

[lean|
theorem max_over_add :
    ∀ (a b c : Int), c + max a b = max (c + a) (c + b) := by blaster
|]

[lean|
theorem min_over_add :
    ∀ (a b c : Int), c + min a b = min (c + a) (c + b) := by blaster
|]

[lean|
theorem max_over_sub2 :
    ∀ (a b c : Int), max a b - c = max (a - c) (b - c) := by blaster
|]

[lean|
theorem min_over_sub2 :
    ∀ (a b c : Int), min a b - c = min (a - c) (b - c) := by blaster
|]

[lean|
theorem derived_n :
    ∀ (available ratio n minFee maxFee price pf : Int),
    let pf := price * (1 + ratio)
    ratio > 0 → ratio <= 100 →
    price > 0 → pf > 0 → minFee >= 0 → maxFee >= minFee → available > 0 →

    (price * n) + min (max minFee (price * n * ratio)) maxFee = available →

    max (min ((available - minFee) / price) (available / pf)) ((available - maxFee) / price) = n := by blaster
|]
