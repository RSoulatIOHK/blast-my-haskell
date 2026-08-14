{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
-- | M3 fixture: class hierarchies with SUPERCLASS constraints, both kinds.
--
-- Task 1 wrote this for OBSERVATION only (`Container`'s `supers: ["Sized"]` in
-- the class-shape dump, and the `$p1Container` selector in the Core dump); the
-- module then degraded loudly, with `Sized t` unsynthesized and the
-- `Container Bag` instance dropped. Task 5 emits superclasses, by two different
-- mechanisms, and both halves live here:
--
--   * `Sized a => Container a` — a USER parent, emitted as Lean
--     `class Container (a : Type) extends Sized a`.
--   * `Ord a => Capped a` — a BUILTIN parent, which cannot ride on `extends`
--     (`Ord`'s Lean image includes `DecidableLT`/`DecidableLE`, which are `def`s,
--     not structures). Its binder recipe is injected at every CONSTRAINT SITE
--     instead, so `Capped a => …` emits `[Ord t] … [BEq t] [Capped t]`.
--
-- See the `M3 Task 5` block in GhcCoreToLean/Tests/Unit.lean for the Lean-side
-- probe transcripts that forced that split, and the `M3 Task 1` block for the
-- recorded dump spines.
module SuperClass where
    import Prelude
    import Lean.Spec (lean)

    class Sized a where
        size :: a -> Int

    class Sized a => Container a where
        empty  :: a
        insert :: Int -> a -> a

    data Bag = Bag Int

    -- The instance that used to be DROPPED whole: neither `empty :: a` (no value
    -- argument at all) nor `insert :: Int -> a -> a` (first argument `Int`) can be
    -- attributed to its instance head by a first-value-argument match, which was
    -- the only attribution there was. Both are now read out of this instance's
    -- dictionary (`Emit.dfunMethodBinds`).
    --
    -- It is declared BEFORE its parent's instance ON PURPOSE. The instance channel
    -- is in source-declaration order, and the emitted child instance omits the
    -- parent field for Lean to fill from the `Sized Bag` instance in scope — so
    -- this order is what makes `Emit.sortInstances` load-bearing rather than
    -- decorative: before the sort existed, this file produced `error: Fields
    -- missing: `size``. MEASURED both ways on a throwaway copy with the two blocks
    -- swapped: the emitted `instance` order is the same either way (parent first),
    -- and only the `$csize` def moves, which is order-irrelevant.
    instance Container Bag where
        empty = Bag 0
        insert k (Bag n) = Bag (n + k)

    instance Sized Bag where
        size (Bag n) = n

    -- Superclass USE site. A `Container a` constraint calling a `Sized` method
    -- is what forces GHC to project the superclass dictionary out of the
    -- `Container` dictionary — the `$p1Container`-style selector Task 1 is
    -- looking for. Without this function the selector never appears anywhere in
    -- the dump (the instance's dfun merely *stores* the parent dict), and the
    -- observation would report a false negative. On the Lean side this is the
    -- `extends` test: the body's `Sized.size` has only `[Container t]` in scope.
    sizeViaContainer :: Container a => a -> Int
    sizeViaContainer x = size x

    bagSize :: Bag -> Int
    bagSize = sizeViaContainer

    bagInsert :: Int -> Bag -> Bag
    bagInsert = insert

    bagEmpty :: Bag
    bagEmpty = empty

    -- BUILTIN superclass. `Level` is an enum so that its derived `Eq` goes through
    -- GHC's tag primops and is reconstructed by Lean `deriving DecidableEq` —
    -- the shape `emitDataDecl` handles; a hand-written or field-wise `Eq` is M3
    -- Task 6's business, not this fixture's.
    data Level = Low | Mid | High deriving (Eq, Ord)

    class Ord a => Capped a where
        cap :: a -> a -> a

    instance Capped Level where
        cap x y = min x y

    -- Only the CHILD's method: needs nothing from the parent.
    capBoth :: Capped a => a -> a -> a
    capBoth x y = cap x y

    -- The PARENT's operator under only the CHILD's constraint — the case the
    -- constraint-site binder injection exists for. Without it the emitted header
    -- is `[Capped t]` alone and `decide (x < y)` cannot elaborate.
    capOrdered :: Capped a => a -> a -> Bool
    capOrdered x y = x < y

    levelCap :: Level -> Level -> Level
    levelCap = capBoth

    levelOrdered :: Level -> Level -> Bool
    levelOrdered = capOrdered

    [lean|
    theorem bagSize_correct :
        ∀ (n : Int), bagSize (Bag.Bag n) = n := by blaster
    |]

    -- `insert`, the method whose `Int` first argument the old attribution could
    -- not place. Quantified, so it pins the whole method body and not one point.
    [lean|
    theorem bagInsert_adds :
        ∀ (k n : Int), bagInsert k (Bag.Bag n) = Bag.Bag (n + k) := by blaster
    |]

    -- `empty`, the method with NO value argument. `rfl`, not `decide`: `Bag`
    -- derives no `Eq` in the Haskell source, so it gets no `DecidableEq` in Lean.
    [lean|
    theorem bagEmpty_zero : bagEmpty = Bag.Bag 0 := by rfl
    |]

    -- The builtin-superclass pair, at the instance head. Ground `decide`: `Level`
    -- is an enum, so these are closed Boolean computations.
    [lean|
    theorem levelCap_takesLower : levelCap Level.High Level.Mid = Level.Mid := by decide
    |]

    [lean|
    theorem levelCap_reflexive : levelCap Level.Low Level.Low = Level.Low := by decide
    |]

    -- `capOrdered` at `Level` is the parent's `<` reached through the child's
    -- constraint: if the `Ord` binder set were missing, this def would not exist.
    [lean|
    theorem levelOrdered_lt : levelOrdered Level.Low Level.High = true := by decide
    |]

    [lean|
    theorem levelOrdered_irreflexive : levelOrdered Level.Mid Level.Mid = false := by decide
    |]
