{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
-- | M3 Task 2 fixture: TWO user classes in one module (the happy path — their
-- method names are DISTINCT, which is the only shape Haskell permits; see the
-- must-fail `TwoClassesSameMethod.hs` for why), plus the one genuinely
-- reachable `methodMap` defect in the same lookup: a LOCAL BINDER whose name
-- equals a class method's.
--
-- `applySizer`'s parameter is called `size`, which is legal Haskell (it shadows
-- the class method; GHC only warns under -Wname-shadowing). Before the M3 Task 2
-- fix, `Emit.emitVar` matched `methodMap` on the bare NAME only, so the
-- reference to the PARAMETER emitted as `Sized.size` — a type-correct,
-- silently-wrong body that ignored the function's argument. The theorem
-- `applySizer_uses_its_argument` below is what discriminates: it holds for the
-- parameter reading and fails for the class-method reading (which is constantly
-- `3`).
module TwoClassesDistinctMethods where
    import Prelude
    import Lean.Spec (lean)

    class Sized a where
        size :: a -> Int

    class Weighed a where
        weight :: a -> Int

    data Box = Box Int
    data Crate = Crate Int

    instance Sized Box where
        size (Box n) = n

    instance Weighed Crate where
        weight (Crate n) = n

    -- Call sites for both classes: each must be rewritten to ITS OWN class's
    -- qualified method (`Sized.size` / `Weighed.weight`).
    boxSize :: Box -> Int
    boxSize b = size b

    crateWeight :: Crate -> Int
    crateWeight c = weight c

    -- The shadowing case (see the header).
    applySizer :: (Box -> Int) -> Int
    applySizer size = size (Box 3)

    [lean|
    theorem boxSize_correct :
        ∀ (n : Int), boxSize (Box.Box n) = n := by blaster

    theorem crateWeight_correct :
        ∀ (n : Int), crateWeight (Crate.Crate n) = n := by blaster

    theorem applySizer_uses_its_argument :
        ∀ (k : Int), applySizer (fun _ => k) = k := by blaster
    |]
