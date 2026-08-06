{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
-- | M3 fixture: a two-level class hierarchy with a SUPERCLASS constraint.
--
-- Task 1 uses this for OBSERVATION only — the class-shape dump must show
-- `Container`'s `supers: ["Sized"]`, and the Core dump must show whatever
-- superclass-selector machinery GHC emits. Emission of `extends`/superclass
-- fields lands in M3 Task 5, so transpiling this module is EXPECTED to degrade
-- (loudly) until then; see the `M3 Task 1` block in GhcCoreToLean/Tests/Unit.lean
-- for the recorded spines.
module SuperClass where
    import Prelude
    import Lean.Spec (lean)

    class Sized a where
        size :: a -> Int

    class Sized a => Container a where
        empty  :: a
        insert :: Int -> a -> a

    data Bag = Bag Int

    instance Sized Bag where
        size (Bag n) = n

    instance Container Bag where
        empty = Bag 0
        insert k (Bag n) = Bag (n + k)

    -- Superclass USE site. A `Container a` constraint calling a `Sized` method
    -- is what forces GHC to project the superclass dictionary out of the
    -- `Container` dictionary — the `$p1Container`-style selector Task 1 is
    -- looking for. Without this function the selector never appears anywhere in
    -- the dump (the instance's dfun merely *stores* the parent dict), and the
    -- observation would report a false negative.
    sizeViaContainer :: Container a => a -> Int
    sizeViaContainer x = size x

    bagSize :: Bag -> Int
    bagSize = sizeViaContainer

    bagInsert :: Int -> Bag -> Bag
    bagInsert = insert

    [lean|
    theorem bagSize_correct :
        ∀ (n : Int), bagSize (Bag.Bag n) = n := by blaster
    |]
