{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
-- | M3 Task 3 fixture: BUILTIN class constraints in a signature.
--
-- `Eq a =>` / `Ord a =>` / `Num a =>` are not user classes, so before this task
-- `stripClassConstraints` left the constraint arrow in place and the dict
-- (already erased at the VALUE level by `Lower`) desynchronised the type: the
-- first value binder got typed as the dictionary. The fix maps each builtin
-- constraint to a Lean instance-implicit binder set (`Maps.classConMap`).
--
-- `maxG` is also the first end-to-end exercise of M1's partial-`maximum` path
-- over a type VARIABLE: its `[Inhabited t]` binder (for the ⊥→`default` image)
-- and the `Ord` binder set have to coexist in one header.
module BuiltinConstraints where

    import Prelude

    -- Eq. The whole body is the builtin `==` at a type variable, so the emitted
    -- def needs exactly `[BEq t]`.
    allSame :: Eq a => a -> a -> Bool
    allSame x y = x == y

    notSame :: Eq a => a -> a -> Bool
    notSame x y = x /= y

    -- Ord. `maximum` is ⊥ on `[]`, so this ALSO needs `[Inhabited t]` (M1's
    -- documented partial-correctness route: faithful on every nonempty list,
    -- `default` exactly where Haskell throws).
    maxG :: Ord a => [a] -> a
    maxG xs = maximum xs

    -- Ord, non-partial. `min`/`max` and a comparison in one body: the binder set
    -- has to cover `Min`/`Max` AND the `decide (· < ·)` image of Haskell `<`.
    clamp :: Ord a => a -> a -> a -> a
    clamp lo hi x = min hi (max lo x)

    ordered :: Ord a => a -> a -> Bool
    ordered x y = x < y

    -- Ord's Eq superclass, used at a type variable: in Haskell an `Ord a`
    -- dictionary yields `==` through `$p1Ord`. The emitted binder set therefore
    -- has to carry `[BEq t]` as well, or this body cannot elaborate.
    ordEq :: Ord a => a -> a -> Bool
    ordEq x y = (x < y) || (x == y)

    -- Num. `+`/`*`/`-`/`negate` only. EVERY numeric literal under a
    -- `Num a`-polymorphic def is deliberately NOT covered and is LOUD — 0 and 1
    -- included, not just "other than 0/1". The blocker is not a missing `OfNat`
    -- binder: `emitLiteral` emits literals Int-ASCRIBED, so `x + 0` emits
    -- `(((· + ·)) x) ((id) ((0 : Int)))` and fails `failed to synthesize
    -- HAdd t Int t` identically at 0, at 1, and even WITH an `[OfNat t 0]` binder
    -- added. `abs`/`signum` are loud here too (their images test `a < 0`, needing
    -- the Ord set a `Num a` constraint does not supply). See `Maps.classConMap`
    -- and the M3 Task 3 block in `GhcCoreToLean/Tests/Unit.lean`.
    double :: Num a => a -> a
    double x = x + x

    sumSquares :: Num a => a -> a -> a
    sumSquares x y = x * x + y * y

    negateBoth :: Num a => a -> a -> a
    negateBoth x y = negate x - y

    -- Monomorphic Int call sites: the polymorphic defs must still be usable
    -- from an unconstrained context.
    allSameInt :: Int -> Int -> Bool
    allSameInt = allSame

    maxGInt :: [Int] -> Int
    maxGInt = maxG

    doubleInt :: Int -> Int
    doubleInt = double

-- The polymorphic defs COMPILING is itself the feature under test (before this
-- task their headers were ill-typed). These theorems additionally pin the
-- semantics at the `Int` instantiation.

{- @lean
theorem allSame_isBEq : ∀ (x y : Int), allSame x y = (x == y) := by blaster
-}

{- @lean
theorem notSame_isNotBEq : ∀ (x y : Int), notSame x y = !(x == y) := by blaster
-}

{- @lean
theorem allSameInt_agrees : ∀ (x y : Int), allSameInt x y = allSame x y := by blaster
-}

{- @lean
theorem ordered_isLt : ∀ (x y : Int), ordered x y = decide (x < y) := by blaster
-}

{- @lean
theorem ordEq_isLe : ∀ (x y : Int), ordEq x y = decide (x ≤ y) := by blaster
-}

-- `maxG` over a two-element list: faithful (nonempty), so no `default` appears.
{- @lean
theorem maxG_pair : ∀ (a b : Int), maxG [a, b] = if a < b then b else a := by blaster
-}

{- @lean
theorem maxG_example : maxG [3, 1, 2] = (3 : Int) := by decide
-}

-- The ⊥ pin, as in ListLibrary's maxOf: Haskell `maximum []` THROWS; the emitted
-- form yields `default` (= 0 at Int) exactly there. A partial-correctness
-- tradeoff, NOT a claim that Haskell returns 0.
{- @lean
theorem maxG_empty_isDefault : maxG ([] : List Int) = 0 := by decide
-}

{- @lean
theorem clamp_middle : clamp (1 : Int) 10 5 = 5 := by decide
-}

{- @lean
theorem clamp_above : clamp (1 : Int) 10 42 = 10 := by decide
-}

{- @lean
theorem double_isAdd : ∀ (x : Int), double x = x + x := by blaster
-}

{- @lean
theorem sumSquares_expand : ∀ (x y : Int), sumSquares x y = x * x + y * y := by blaster
-}

{- @lean
theorem negateBoth_expand : ∀ (x y : Int), negateBoth x y = -x - y := by blaster
-}
