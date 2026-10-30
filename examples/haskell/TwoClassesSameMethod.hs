{-# OPTIONS_GHC -fplugin GhcDump.Plugin #-}
-- NEGATIVE fixture: this module does not compile, so `./transpile.sh
-- examples/haskell/TwoClassesSameMethod.hs` is expected to exit NON-zero at the
-- *cabal build* stage (GHC refuses it; the transpiler is never reached) and no
-- GhcCoreToLean/Generated/TwoClassesSameMethod.lean is produced. Deliberately
-- EXCLUDED from the green-regression list, like NewtypeInstances.hs — but note
-- the failure is GHC's, not a transpiler refusal.
--
-- WHY IT IS HERE. M3 Task 2 set out to fix `Emit.methodMap` being keyed by bare
-- method name: two classes declaring `size` produce two entries and `emitVar`
-- took the first by instance-dump order. This file is the attempt to exhibit
-- that ambiguity in ONE module, and it pins the reason you cannot: class methods
-- are top-level names in the module namespace, so a second class declaring
-- `size` is a duplicate declaration. Observed under the pipeline's GHC 9.2.7
-- (`./transpile.sh …` exits 1; the message carries no error code — those start
-- at GHC 9.6):
--
--     TwoClassesSameMethod.hs:41:9: error:
--         Multiple declarations of ‘size’
--         Declared at: TwoClassesSameMethod.hs:38:9
--                      TwoClassesSameMethod.hs:41:9
--
-- So the same-name ambiguity is reachable only when the two classes live in
-- DIFFERENT modules and this module instantiates both (then
-- `Emit.reconstructClasses` rebuilds the imported class from its local
-- instance's `$c` binds and the bare key collides). `Emit.sameMethodAmbiguities`
-- refuses exactly that, and `Main.lean` reports it before any emission — an
-- unexercised tripwire, since cross-module user classes are not supported
-- end-to-end (an imported class's method reference arrives module-qualified,
-- misses the bare `methodMap` key, and fails loud at `lake build`).
--
-- The happy path — two classes whose method names DIFFER, which is the only
-- shape Haskell permits — is `TwoClassesDistinctMethods.hs`, which also pins the
-- one genuinely reachable defect in the same lookup (a local binder shadowing a
-- method name).
module TwoClassesSameMethod where
    import Prelude

    class Sized a where
        size :: a -> Int

    class Weighed a where
        size :: a -> Int

    data Box = Box Int
    data Crate = Crate Int

    instance Sized Box where
        size (Box n) = n

    instance Weighed Crate where
        size (Crate n) = n

    boxSize :: Box -> Int
    boxSize b = size b
