{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
-- | M3 Task 4 fixture: a class with a DEFAULT METHOD body, one instance that
-- OVERRIDES it and one that RELIES on it.
--
-- The default (`greet x = name x + 1`) is written in terms of the class's other
-- method, so GHC compiles it to a top-level `$dmgreet` that takes the class
-- dictionary. The two instances discriminate the two behaviours: `Loud`
-- multiplies by ten, `Quiet` must pick up the `+ 1` default. A transpiler that
-- dropped the default silently would leave `quietGreet` either unbuildable
-- (loud) or — if it fell back to the override's body — provably wrong against
-- `quietGreet_uses_the_default` below.
module DefaultMethods where
    import Prelude
    import Lean.Spec (lean)

    class Greet a where
        name  :: a -> Int
        greet :: a -> Int
        greet x = name x + 1

    data Loud  = Loud Int
    data Quiet = Quiet Int

    -- OVERRIDES the default. The override matches on the constructor rather
    -- than calling `name` (`greet x = name x * 10`), which is a shape the
    -- transpiler cannot emit: calling a SIBLING method needs the instance's own
    -- dictionary, so GHC's `$cgreet` references the dfun, and the emitted def —
    -- which precedes the instance, as Lean instances are not forward-visible —
    -- fails with `failed to synthesize Greet ?m`. Recorded verbatim in the M3
    -- Task 4 block of GhcCoreToLean/Tests/Unit.lean.
    instance Greet Loud where
        name (Loud n) = n
        greet (Loud n) = n * 10

    -- RELIES on the default: no `greet` at all.
    instance Greet Quiet where
        name (Quiet n) = n

    -- Call sites for both, through the class method (not the instance body), so
    -- the dispatch itself is what the theorems check.
    loudGreet :: Loud -> Int
    loudGreet = greet

    quietGreet :: Quiet -> Int
    quietGreet = greet

    -- The non-defaulted method still has to work at both instances.
    loudName :: Loud -> Int
    loudName = name

    quietName :: Quiet -> Int
    quietName = name

    [lean|
    theorem loudName_correct :
        ∀ (n : Int), loudName (Loud.Loud n) = n := by blaster

    theorem quietName_correct :
        ∀ (n : Int), quietName (Quiet.Quiet n) = n := by blaster

    -- The OVERRIDE: `greet (Loud n) = n * 10`, not the class default.
    theorem loudGreet_overrides_the_default :
        ∀ (n : Int), loudGreet (Loud.Loud n) = n * 10 := by blaster

    -- The DEFAULT: `greet x = name x + 1`, inherited from the class body.
    theorem quietGreet_uses_the_default :
        ∀ (n : Int), quietGreet (Quiet.Quiet n) = n + 1 := by blaster

    -- The two readings are not interchangeable: at n = 3 the override gives 30
    -- and the default gives 4. Ground, so `decide` (kernel evaluation) rather
    -- than blaster — this is the witness that the two theorems above are not
    -- simultaneously satisfiable by one shared body.
    theorem override_and_default_differ :
        loudGreet (Loud.Loud 3) = 30 ∧ quietGreet (Quiet.Quiet 3) = 4 := by decide
    |]
