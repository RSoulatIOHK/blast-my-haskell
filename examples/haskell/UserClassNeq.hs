{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
-- | M3 Task 2 fixture: a USER class that declares the operator `/=` (legal with
-- `import Prelude hiding ((/=))`).
--
-- `Main.lean` used to drop every bind named `$c/=` unconditionally — the rule
-- exists for GHC's auto-derived `Eq` method, which Lean's `BEq` supplies itself
-- and whose body cannot elaborate (it references the Eq dict, and `$c…` defs are
-- emitted before the instances). Applied by name, it also ate THIS class's
-- method: `emitInstanceUser` then found no `$c` bind for the only method it
-- needed and dropped the whole instance, so `differs` failed to synthesize at
-- `lake build`. The drop is now scoped to the heads of the module's `Eq`
-- instances (`Emit.isEqNeqBind`), and this module has none.
--
-- The instance is deliberately ONE equation over a single-constructor type: a
-- multi-equation method (e.g. over `data Coin = Heads | Tails`) makes GHC build a
-- `fail` join point applied to `void#`, which has no `Maps.valueMap` image — a
-- real but UNRELATED gap (it shows up as `GHC.Prim.void_hash_` in the emitted
-- body and fails loud at `lake build`).
module UserClassNeq where
    import Prelude hiding ((/=))
    import Lean.Spec (lean)

    class Neq a where
        (/=) :: a -> a -> Bool

    data Box = Box Int

    instance Neq Box where
        (Box a) /= (Box b) = a > b || b > a

    differs :: Box -> Box -> Bool
    differs a b = a /= b

    [lean|
    theorem differs_is_inequality :
        ∀ (m n : Int), differs (Box.Box m) (Box.Box n) = (!(m == n)) := by blaster
    |]
